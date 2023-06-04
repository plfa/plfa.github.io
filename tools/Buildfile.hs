{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant <&>" #-}
{-# HLINT ignore "Monad law, left identity" #-}

module Main where

import Buildfile.Author (Author (..))
import Buildfile.Book (Book (..), Chapter (..), ChapterTable, Part (..), fromBook, nextChapter, previousChapter)
import Buildfile.Contributor (Contributor (..))
import Buildfile.Script qualified as Script (fromFilePath, inline)
import Buildfile.Stylesheet (Stylesheet (stylesheetEnabled, stylesheetId))
import Buildfile.Stylesheet qualified as Stylesheet (alternate, fromFilePath)
import Control.Exception (assert, catch)
import Control.Monad (forM, forM_, unless, when, (>=>))
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State (evalState)
import Data.ByteString.Lazy qualified as LazyByteString
import Data.ByteString.Lazy.Base64 qualified as LazyByteString
import Data.Default.Class (Default (def))
import Data.Digest.Pure.SHA qualified as Digest (bytestringDigest, sha512)
import Data.Either (fromRight, isRight)
import Data.Function (on, (&))
import Data.Functor ((<&>))
import Data.Hashable (Hashable)
import Data.List (isPrefixOf, sortBy)
import Data.List qualified as List
import Data.Maybe (fromMaybe, isJust, isNothing, maybeToList)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Text.Lazy qualified as LazyText
import Data.Text.Lazy.Encoding qualified as LazyText
import Data.Traversable (for)
import GHC.Generics (Generic)
import GHC.Stack.Types (HasCallStack)
import Shoggoth.Agda qualified as Agda
import Shoggoth.Configuration
import Shoggoth.Metadata
import Shoggoth.PostInfo
import Shoggoth.Prelude
import Shoggoth.Routing (Router (..), RoutingTable, Stages (..), permalinkRouter)
import Shoggoth.Routing qualified as Route
import Shoggoth.TagSoup qualified as TagSoup
import Shoggoth.Template.Pandoc (Extension (..), HTMLMathMethod (..), HighlightStyle, Inlines, Lang, Locale, MetaValue, ObfuscationMethod (..), Pandoc (..), ReaderOptions (..), Reference, WriterOptions (..), defaultKaTeXURL, extensionsFromList, runPandoc, runPandocWith)
import Shoggoth.Template.Pandoc qualified as Pandoc
import Shoggoth.Template.Pandoc.Builder qualified as Builder
import Shoggoth.Template.Pandoc.Citeproc qualified as Citeproc
import System.Directory (findExecutable, makeAbsolute)
import System.Exit (ExitCode (..), exitWith)
import Text.Printf (printf)

outDir, tmpDir :: FilePath
outDir = "_site"
tmpDir = "_cache"

dataDir, authorDir, contributorDir, bibliographyFile, tableOfContentsFile :: FilePath
dataDir = "data"
authorDir = dataDir </> "authors"
contributorDir = dataDir </> "contributors"
tableOfContentsFile = dataDir </> "tableOfContents.yml"
bibliographyFile = dataDir </> "bibliography.bib"

bookDir, chapterDir, courseDir :: FilePath
bookDir = "book"
chapterDir = "src"
courseDir = "courses"

epubDir, epubFontsDir, epubStyleDir, epubTemplateDir :: FilePath
epubDir = bookDir </> "epub"
epubFontsDir = epubDir </> "fonts"
epubStyleDir = epubDir </> "sass"
epubTemplateDir = epubDir </> "templates"

webDir, webAssetDir, webPostDir, webStyleDir, webTemplateDir :: FilePath
webDir = "web"
webAssetDir = webDir </> "assets"
webPostDir = webDir </> "posts"
webStyleDir = webDir </> "sass"
webTemplateDir = webDir </> "templates"

tmpRawAgdaHtmlDir, tmpAgdaHtmlDir, tmpBodyHtmlDir, tmpEpubDir :: FilePath
tmpRawAgdaHtmlDir = tmpDir </> "raw_agda_html" -- Compile literate Agda code blocks to raw HTML
tmpAgdaHtmlDir = tmpDir </> "agda_html" -- Fix Agda HTML output
tmpBodyHtmlDir = tmpDir </> "body_html" -- Compile Markdown to HTML
tmpEpubDir = tmpDir </> "epub"

--------------------------------------------------------------------------------
-- Rules

main :: IO ()
main = do
  absTmpDir <- makeAbsolute tmpDir
  shakeArgs
    shakeOptions
      { shakeFiles = tmpDir,
        shakeProgress = progressSimple,
        shakeExtra =
          mempty
            & addShakeExtra (OutputDirectory outDir)
            & addShakeExtra (CacheDirectory absTmpDir)
            & addShakeExtra (TemplateDirectory webTemplateDir)
            & addShakeExtra readerOpts
            & addShakeExtra writerOpts
      }
    $ do
      --------------------------------------------------------------------------------
      -- Agda resource & libraries

      agda <- newResource "agda" 1
      Agda.makeVersionOracle
      Agda.makeStandardLibraryOracle "standard-library"

      getAgdaFileInfo <- newCache $ \src -> do
        project <- failOnError $ getProject src
        agdaLibraries <- getAgdaLibrariesForProject project
        fileInfo@Agda.AgdaFileInfo {library, libraryIncludePath, outputFileForHtml, moduleName} <-
          failOnError $ Agda.resolveFileInfo agdaLibraries src
        -- NOTE: Each Agda file compiles to its own directory, i.e., the
        --       `agdaHtmlPathName` is included in the path. Otherwise,
        --       Agda will regenerate files it already generated in a
        --       previous task, and you'll get an error saying that the
        --       temporary file has "changed since being depended upon".
        let libraryRawAgdaHtmlDir = tmpRawAgdaHtmlDir </> Text.unpack moduleName </> Agda.libraryRoot library </> libraryIncludePath
        let rawAgdaHtmlPath = libraryRawAgdaHtmlDir </> outputFileForHtml
        let agdaHtmlPath = tmpAgdaHtmlDir </> replaceExtensions src (takeExtension outputFileForHtml)
        return (RichAgdaFileInfo fileInfo libraryRawAgdaHtmlDir rawAgdaHtmlPath agdaHtmlPath project agdaLibraries)

      --------------------------------------------------------------------------------
      -- Routing table

      let postOrPermalinkRouter :: FilePath -> Action FilePath
          postOrPermalinkRouter src
            | isPostSource src = do
                PostInfo {..} <- failOnError $ parsePostSource (takeFileName src)
                return $ outDir </> postYear </> postMonth </> postDay </> postSlug </> "index.html"
            | otherwise = permalinkRouter src

      let postOrPermalinkRouterWithAgda :: FilePath -> Action Stages
          postOrPermalinkRouterWithAgda src = do
            let bodyHtml = tmpBodyHtmlDir </> replaceExtensions src "html"
            out <- postOrPermalinkRouter src
            let commonStages = "body_html" :@ bodyHtml :> Output out
            if Agda.isAgdaFile src
              then do
                AgdaFileInfo {rawAgdaHtmlPath, agdaHtmlPath} <- getAgdaFileInfo src
                return $ rawAgdaHtmlPath :> "agda_html" :@ agdaHtmlPath :> commonStages
              else return commonStages

      let ?routingTable =
            mconcat
              [ -- Book (Web Version)
                ["README.md"] |-> postOrPermalinkRouterWithAgda,
                ["CONTRIBUTING.md"] |-> postOrPermalinkRouterWithAgda,
                [webDir </> "TableOfContents.md"] |-> postOrPermalinkRouterWithAgda,
                [chapterDir </> "plfa" <//> "*.md"] *|-> postOrPermalinkRouterWithAgda,
                -- Book (Standalone HTML)
                Route.create (outDir </> "plfa.html"),
                -- Book (EPUB Version)
                Route.create (outDir </> "plfa.epub"),
                -- Announcements
                [webDir </> "Announcements.md"] |-> postOrPermalinkRouterWithAgda,
                [webDir </> "rss.xml"] |-> outDir </> "rss.xml",
                [webPostDir <//> "*.md"] *|-> postOrPermalinkRouterWithAgda,
                -- Documentation
                [webDir </> "Citing.md"] |-> postOrPermalinkRouterWithAgda,
                [webDir </> "Notes.md"] |-> postOrPermalinkRouterWithAgda,
                [webDir </> "StyleGuide.md"] |-> postOrPermalinkRouterWithAgda,
                -- Courses
                [courseDir <//> "*.md"] *|-> postOrPermalinkRouterWithAgda,
                [courseDir <//> "*.pdf"] *|-> \src -> outDir </> makeRelative courseDir src,
                -- Assets
                [webDir </> "404.md"] |-> permalinkRouter,
                [webStyleDir </> "light.scss"] |-> outDir </> "assets/css/light.css",
                [webStyleDir </> "dark.scss"] |-> outDir </> "assets/css/dark.css",
                Route.create (outDir </> "assets/css/highlight.css"),
                [webAssetDir <//> "*"] *|-> \src -> outDir </> "assets" </> makeRelative webAssetDir src
              ]

      --------------------------------------------------------------------------------
      -- Caches

      getAuthors <- newCache $ \() -> do
        authorFiles <- getDirectoryFiles authorDir ["*.yml"]
        authors <- traverse (\src -> readYaml $ authorDir </> src) authorFiles
        return (authors :: [Author])
      let ?getAuthors = getAuthors

      getContributors <- newCache $ \() -> do
        contributorFiles <- getDirectoryFiles "" [contributorDir </> "*.yml"]
        contributors <- traverse readYaml contributorFiles
        let sortedContributors = sortBy (compare `on` contributorCount) contributors
        return (sortedContributors :: [Contributor])

      getTableOfContents <- newCache $ \() -> do
        readYaml @Book tableOfContentsFile
      let ?getTableOfContents = getTableOfContents

      getChapterTable <- newCache $ \() -> do
        fromBook <$> getTableOfContents ()
      let ?getChapterTable = getChapterTable

      getDefaultMetadata <- newCache $ \() -> do
        metadata <- readYaml @Metadata (dataDir </> "metadata.yml")
        authorField <- constField "author" <$> ?getAuthors ()
        buildDateField <- currentDateField "%Y-%m" "build_date"
        buildDateRfc822Field <- currentDateField rfc822DateFormat "build_date_rfc822"
        return $ mconcat [metadata, authorField, buildDateField, buildDateRfc822Field]
      let ?getDefaultMetadata = getDefaultMetadata

      getReferences <- newCache $ \() -> do
        bibliographyFileBody <- readFile' bibliographyFile
        bibliographyFileDoc@(Pandoc meta _) <- runPandoc $ Pandoc.readBibTeX readerOpts bibliographyFileBody
        case Pandoc.lookupMeta "references" meta of
          Just references -> return references
          Nothing -> fail $ printf "Could not read references from '%s'" bibliographyFile
      let ?getReferences = getReferences

      getAgdaLinkFixer <- newCache $ \src -> do
        info@AgdaFileInfo {moduleName, project, libraries} <- getAgdaFileInfo src
        standardLibrary <- Agda.getStandardLibrary
        Agda.makeAgdaLinkFixer (Just standardLibrary) (List.delete standardLibrary libraries) []

      getTemplateFile <- Pandoc.makeCachedTemplateFileGetter
      let ?getTemplateFile = getTemplateFile

      getDigest <- newCache $ \src ->
        getMode >>= \case
          Development -> return Nothing
          Production -> do
            need [src]
            liftIO $ do
              stream <- LazyByteString.readFile src
              let digest = Digest.sha512 stream
              return . Just $ "sha512-" <> LazyByteString.encodeBase64 (Digest.bytestringDigest digest)
      let ?getDigest = getDigest

      --------------------------------------------------------------------------------
      -- Phony targets

      "build" ~> do
        need =<< Route.outputs

      let clean = do
            removeFilesAfter tmpRawAgdaHtmlDir ["//*"]
            removeFilesAfter tmpAgdaHtmlDir ["//*"]
            removeFilesAfter tmpBodyHtmlDir ["//*"]
            removeFilesAfter tmpEpubDir ["//*"]

      "clean" ~> clean

      let clobber = do
            clean
            removeFilesAfter outDir ["//*"]

      "clobber" ~> clobber

      --------------------------------------------------------------------------------
      -- Table of Contents

      let getTableOfContentsField () = do
            tocMetadata <- toMetadata <$> getTableOfContents ()
            tocResolved <- resolveIncludes (fmap fst . getFileWithMetadata) tocMetadata
            return $ constField "toc" tocResolved

      -- Build /
      outDir </> "index.html" %> \out -> do
        src <- Route.source out
        tocField <- getTableOfContentsField ()
        (fileMetadata, indexMarkdownTemplate) <- getFileWithMetadata src
        stylesheetField <- getStylesheetField
        scriptField <- getScriptField
        let metadata = mconcat [tocField, fileMetadata, stylesheetField, scriptField]
        return indexMarkdownTemplate
          >>= Pandoc.applyAsTemplate metadata
          >>= markdownToHtml5
          >>= Pandoc.applyTemplates ["page.html", "default.html"] metadata
          >>= writeHtml5 outDir out

      --------------------------------------------------------------------------------
      -- Compile Markdown & Agda to HTML

      -- Stage 1: Compile literate Agda code blocks to raw HTML
      tmpRawAgdaHtmlDir <//> "*.md" %> \next -> do
        (src, prev) <- (,) <$> Route.source next <*> Route.prev next
        Agda.getVersion
        AgdaFileInfo {libraryRawAgdaHtmlDir, libraries} <- getAgdaFileInfo src
        need [prev]
        withResource agda 1 $
          Agda.compileTo Agda.Html libraries libraryRawAgdaHtmlDir prev

      -- Stage 2: Fix raw Agda HTML output
      tmpAgdaHtmlDir <//> "*.md" %> \next -> do
        (src, prev) <- (,) <$> Route.source next <*> Route.prev next
        need [prev]
        RichAgdaFileInfo {agdaFileInfo} <- getAgdaFileInfo src
        agdaLinkFixer <- getAgdaLinkFixer src
        readFileWithMetadata prev
          <&> snd
          <&> TagSoup.parseTagsOptions (TagSoup.parseOptionsEntities (const Nothing)) {TagSoup.optTagPosition = True}
          <&> Agda.runAgdaSoup . traverse (Agda.qualifyIdSoup agdaFileInfo . TagSoup.mapUrls agdaLinkFixer)
          <&> TagSoup.renderTagsOptions TagSoup.renderOptions {TagSoup.optEscape = id}
          >>= writeFile' next

      -- Stage 3: Compile Markdown to HTML
      tmpBodyHtmlDir <//> "*.html" %> \next -> do
        (src, prev, out) <- (,,) <$> Route.source next <*> Route.prev next <*> Route.output next
        readFile' prev
          >>= markdownToHtml5
          >>= writeFile' next

      -- Stage 4: Apply HTML templates
      outDir <//> "*.html" %> \out -> do
        (src, prev) <- (,) <$> Route.source out <*> Route.prev out
        (fileMetadata, htmlBody) <- getFileWithMetadata prev
        stylesheetField <- getStylesheetField
        scriptField <- getScriptField
        let metadata = mconcat [fileMetadata, stylesheetField, scriptField]
        let htmlTemplates
              | isPostSource src = ["post.html", "default.html"]
              | otherwise = ["page.html", "default.html"]
        html <- Pandoc.applyTemplates htmlTemplates metadata htmlBody
        html <- postProcessHtml5 outDir out html
        writeFile' out html

      --------------------------------------------------------------------------------
      -- Posts

      let getPostsField () = do
            posts <- filter isPostSource <$> Route.sources
            postsMetadata <- forM posts $ \post -> do
              bodyHtml <- Route.anchor "body_html" post
              (fileMetadata, body) <- getFileWithMetadata bodyHtml
              let bodyHtmlField = constField "body_html" body
              url <- failOnError $ fileMetadata ^. "url"
              let htmlTeaserField = ignoreError $ htmlTeaserFieldFromHtml url body "teaser_html"
              let textTeaserField = ignoreError $ textTeaserFieldFromHtml body "teaser_plain"
              return $ mconcat [fileMetadata, bodyHtmlField, htmlTeaserField, textTeaserField]
            return $ constField "post" (reverse postsMetadata)

      -- Build /Announcements/index.html
      outDir </> "Announcements" </> "index.html" %> \out -> do
        src <- Route.source out
        postsField <- getPostsField ()
        (fileMetadata, indexMarkdownTemplate) <- getFileWithMetadata src
        stylesheetField <- getStylesheetField
        scriptField <- getScriptField
        let metadata = mconcat [postsField, fileMetadata, stylesheetField, scriptField]
        return indexMarkdownTemplate
          >>= Pandoc.applyAsTemplate metadata
          >>= markdownToHtml5
          >>= Pandoc.applyTemplates ["page.html", "default.html"] metadata
          >>= writeHtml5 outDir out

      -- Build /Acknowledgements/index.html
      outDir </> "Acknowledgements" </> "index.html" %> \out -> do
        src <- Route.source out
        contributorField <- constField "contributor" <$> getContributors ()
        (fileMetadata, acknowledgmentsMarkdownTemplate) <- getFileWithMetadata src
        stylesheetField <- getStylesheetField
        scriptField <- getScriptField
        let metadata = mconcat [contributorField, fileMetadata, stylesheetField, scriptField]
        return acknowledgmentsMarkdownTemplate
          >>= Pandoc.applyAsTemplate metadata
          >>= markdownToHtml5
          >>= Pandoc.applyTemplates ["page.html", "default.html"] metadata
          >>= writeHtml5 outDir out

      -- Build rss.xml
      outDir </> "rss.xml" %> \out -> do
        src <- Route.source out
        postsField <- getPostsField ()
        (fileMetadata, rssXmlTemplate) <- getFileWithMetadata src
        let metadata = mconcat [postsField, fileMetadata]
        return rssXmlTemplate
          >>= Pandoc.applyAsTemplate metadata
          >>= writeFile' out

      --------------------------------------------------------------------------------
      -- Assets

      -- Build 404.html
      outDir </> "404.html" %> \out -> do
        src <- Route.source out
        (fileMetadata, errorMarkdownBody) <- getFileWithMetadata src
        stylesheetField <- getStylesheetField
        scriptField <- getScriptField
        let metadata = mconcat [fileMetadata, stylesheetField, scriptField]
        return errorMarkdownBody
          >>= markdownToHtml5
          >>= Pandoc.applyTemplates ["page.html", "default.html"] metadata
          >>= writeHtml5 outDir out

      -- Build assets/css/light.css
      outDir </> "assets/css/light.css" %> \out -> do
        src <- Route.source out
        need =<< getDirectoryFiles "" [webStyleDir <//> "*.scss"]
        sass [] ["--load-path=" <> webStyleDir, "--style=compressed", src, out] Nothing

      -- Build assets/css/dark.css
      outDir </> "assets/css/dark.css" %> \out -> do
        src <- Route.source out
        need =<< getDirectoryFiles "" [webStyleDir <//> "*.scss"]
        sass [] ["--load-path=" <> webStyleDir, "--style=compressed", src, out] Nothing

      -- Build assets/css/highlight.css
      outDir </> "assets/css/highlight.css" %> \out -> do
        sass [] ["--style=compressed", out] (Just $ LazyText.pack highlightCss)

      -- Copy static assets
      outDir </> "assets" <//> "*" %> \out -> do
        src <- Route.source out
        copyFile' src out

      -- Copy course PDFs
      --
      -- TODO: build from source instead of copying
      -- TODO: remove PDFs from repository
      --
      outDir <//> "*.pdf" %> \out -> do
        src <- Route.source out
        copyFile' src out

      --------------------------------------------------------------------------------
      -- Standalone HTML

      outDir </> "plfa.html" %> \out -> do
        -- Require all assets, rss.xml, and standalone template:
        assets <- filter ((outDir </> "assets" <//> "*") ?==) <$> Route.outputs
        need assets
        need [outDir </> "rss.xml", webTemplateDir </> "standalone.html"]

        defaultMetadata <- ?getDefaultMetadata ()

        let routeChapter src =
              if Agda.isAgdaFile src then Route.anchor "agda_html" src else return src

        bookDoc <- makeBookDoc routeChapter

        standaloneHtmlTemplate <- Pandoc.compileTemplateFile (webTemplateDir </> "standalone.html")

        let writerOptsForStandaloneHtml =
              writerOpts
                { writerTemplate = Just standaloneHtmlTemplate,
                  writerTableOfContents = True,
                  writerCiteMethod = Pandoc.Natbib,
                  writerWrapText = Pandoc.WrapPreserve,
                  writerTopLevelDivision = Pandoc.TopLevelPart,
                  writerTOCDepth = 2,
                  writerReferenceLocation = Pandoc.EndOfDocument
                }

        let pandocToStandaloneHtml doc = do
              html5 <- runPandoc (Pandoc.writeHtml5String writerOptsForStandaloneHtml doc)
              html5 <- postProcessHtml5 outDir out html5
              runPandoc $ do
                Pandoc.setResourcePath [outDir]
                Pandoc.makeSelfContained html5

        return bookDoc
          >>= pandocToStandaloneHtml
          >>= writeFile' out

      --------------------------------------------------------------------------------
      -- EPUB

      -- Polish EPUB with Calibre
      outDir </> "plfa.epub" %> \out -> do
        let src = tmpEpubDir </> "plfa_unpolished.epub"
        need [src]
        maybeEbookPolish <- liftIO $ findExecutable "ebook-polish"
        case maybeEbookPolish of
          Nothing -> do
            putWarn "Could not find 'ebook-publish' on the PATH; plfa.epub is unpolished"
            copyFile' src out
          Just ebookPolish -> do
            command
              []
              ebookPolish
              [ "--smarten-punctuation",
                "--remove-unused-css",
                "--add-soft-hyphens",
                "--upgrade-book",
                "--jacket",
                "--embed-fonts",
                "--subset-fonts",
                src,
                out
              ]

      -- Build unpolished EPUB
      tmpEpubDir </> "plfa_unpolished.epub" %> \out -> do
        -- Require metadata and stylesheet
        need [tmpEpubDir </> "epub-metadata.xml", tmpEpubDir </> "style.css"]

        let routeChapter src =
              if Agda.isAgdaFile src then Route.anchor "agda_html" src else return src

        bookDoc <-
          makeBookDoc routeChapter
            <&> Pandoc.setMeta "css" [tmpEpubDir </> "style.css"]
            <&> Pandoc.setMeta "highlighting-css" highlightCss

        -- Set writer options
        epubMetadata <- readFile' (tmpEpubDir </> "epub-metadata.xml")
        epubFonts <- getDirectoryFiles "" [epubFontsDir </> "*.ttf"]
        epubTemplate <- Pandoc.compileTemplateFile (epubTemplateDir </> "epub.html")

        let writerOptsForEpub =
              writerOpts
                { writerTemplate = Just epubTemplate,
                  writerTableOfContents = True,
                  writerCiteMethod = Pandoc.Natbib,
                  writerWrapText = Pandoc.WrapPreserve,
                  writerTopLevelDivision = Pandoc.TopLevelPart,
                  writerEpubMetadata = Just epubMetadata,
                  writerEpubFonts = epubFonts,
                  writerSplitLevel = 2,
                  writerTOCDepth = 2,
                  writerReferenceLocation = Pandoc.EndOfDocument
                }

        epub <- runPandoc $ Pandoc.writeEPUB3 writerOptsForEpub bookDoc
        liftIO $ LazyByteString.writeFile out epub

      -- Build EPUB metadata
      tmpEpubDir </> "epub-metadata.xml" %> \out -> do
        let src = epubTemplateDir </> "epub-metadata.xml"
        defaultMetadata <- getDefaultMetadata ()
        contributors <- getContributors ()
        let metadata = mconcat [defaultMetadata, constField "contributor" contributors]
        readFile' src
          >>= Pandoc.applyAsTemplate metadata
          >>= writeFile' out

      -- Build EPUB stylesheet
      tmpEpubDir </> "style.css" %> \out -> do
        let src = epubStyleDir </> "style.scss"
        need =<< getDirectoryFiles "" [epubStyleDir <//> "*.scss"]
        sass [] ["--load-path=" <> epubStyleDir, "--style=compressed", src, out] Nothing

--------------------------------------------------------------------------------
-- Agda

data Project
  = Main
  | Post
  | Course {courseId :: String}
  deriving (Show, Typeable, Eq, Generic, Hashable, Binary, NFData)

getCourseId :: MonadError String m => FilePath -> m String
getCourseId src
  | courseDir `List.isPrefixOf` src = return $ makeRelative courseDir (takeDirectory src)
  | otherwise = throwError $ printf "Courses must be in '%s', '%s':" courseDir src

getProject :: MonadError String m => FilePath -> m Project
getProject src
  | chapterDir `List.isPrefixOf` src = return Main
  | courseDir `List.isPrefixOf` src = Course <$> getCourseId src
  | webPostDir `List.isPrefixOf` src = return Post
  | otherwise = throwError $ printf "Not part of an Agda project: '%s'" src

getAgdaLibrariesForProject :: Project -> Action [Agda.Library]
getAgdaLibrariesForProject project = do
  standardLibrary <- Agda.getStandardLibrary
  return $
    case project of
      Main -> [standardLibrary, mainLibrary]
      Post -> [standardLibrary, mainLibrary, postLibrary]
      Course courseId -> [standardLibrary, mainLibrary, courseLibrary]
        where
          courseLibrary :: Agda.Library
          courseLibrary =
            Agda.Library
              { libraryName = Text.replace "/" "." (Text.pack courseId),
                libraryRoot = courseDir </> courseId,
                includePaths = ["."],
                canonicalBaseUrl = "https://plfa.github.io/" <> Text.pack courseId
              }

mainLibrary :: Agda.Library
mainLibrary =
  Agda.Library
    { libraryName = "plfa",
      libraryRoot = chapterDir,
      includePaths = ["."],
      canonicalBaseUrl = "https://plfa.github.io/"
    }

postLibrary :: Agda.Library
postLibrary =
  Agda.Library
    { libraryName = "announcements",
      libraryRoot = webPostDir,
      includePaths = ["."],
      canonicalBaseUrl = "https://plfa.github.io/"
    }

--------------------------------------------------------------------------------
-- Posts

-- match posts/YYYY-MM-DD-<slug><file-extensions>
isPostSource :: FilePath -> Bool
isPostSource src = isRight $ parsePostSource (makeRelative webPostDir src)

-- match _site/YYYY/MM/DD/<slug>/index.html
isPostOutput :: FilePath -> Bool
isPostOutput out = isRight $ parsePostOutput (makeRelative outDir out)

--------------------------------------------------------------------------------
-- File Reader

getScriptField ::
  ( ?getDigest :: FilePath -> Action (Maybe LazyText.Text),
    ?routingTable :: RoutingTable
  ) =>
  Action Metadata
getScriptField = do
  anchorjs <- Script.fromFilePath (outDir </> "assets/js/anchor.js")
  darkmode <- Script.fromFilePath (outDir </> "assets/js/darkmode.js")
  main <- Script.fromFilePath (outDir </> "assets/js/main.js")
  return $ constField "script" [anchorjs, darkmode, main]

getStylesheetField ::
  ( ?getDigest :: FilePath -> Action (Maybe LazyText.Text),
    ?routingTable :: RoutingTable
  ) =>
  Action Metadata
getStylesheetField = do
  light <- Stylesheet.fromFilePath (outDir </> "assets/css/light.css")
  dark <- Stylesheet.alternate <$> Stylesheet.fromFilePath (outDir </> "assets/css/dark.css")
  return $ constField "stylesheet" [light, dark]

getFileWithMetadata ::
  ( ?getDefaultMetadata :: () -> Action Metadata,
    ?getChapterTable :: () -> Action ChapterTable,
    ?routingTable :: RoutingTable
  ) =>
  FilePath ->
  Action (Metadata, Text)
getFileWithMetadata cur = do
  (src, out, url) <- (,,) <$> Route.source cur <*> Route.output cur <*> Route.url cur

  -- Default metadata:
  defaultMetadata <- ?getDefaultMetadata ()

  -- Metadata from source file and body from current file:
  (head, body) <-
    if src == cur
      then do
        readFileWithMetadata src
      else do
        (head, _) <- readFileWithMetadata src
        (_, body) <- readFileWithMetadata cur
        return (head, body)

  let titleVariants = ignoreError $ titleVariantMetadata <$> head ^. "title"
  let sourceField = constField "source" src
  let bodyField = constField "body" body
  let urlField = constField "url" url

  -- Previous and next chapter URLs:
  chapterTable <- ?getChapterTable ()
  maybePrevUrl <- traverse Route.url (previousChapter chapterTable src)
  let prevField = ignoreNothing $ constField "prev" <$> maybePrevUrl
  maybeNextUrl <- traverse Route.url (nextChapter chapterTable src)
  let nextField = ignoreNothing $ constField "next" <$> maybeNextUrl

  -- Dates:
  modifiedDateField <- lastModifiedISO8601Field src "modified_date"
  let dateField = fromRight mempty $ postDateField "%a %-d %b, %Y" src "date"
  let dateRfc822Field = fromRight mempty $ postDateField rfc822DateFormat src "date_rfc822"

  let metadata =
        mconcat
          [ defaultMetadata,
            head,
            urlField,
            bodyField,
            titleVariants,
            sourceField,
            prevField,
            nextField,
            modifiedDateField,
            dateField,
            dateRfc822Field
          ]

  return (metadata, body)

--------------------------------------------------------------------------------
-- Create Pandoc document for book (for single-document formats)

makeBookDoc ::
  ( ?getDefaultMetadata :: () -> Action Metadata,
    ?getChapterTable :: () -> Action ChapterTable,
    ?getTableOfContents :: () -> Action Book,
    ?getAuthors :: () -> Action [Author],
    ?getReferences :: () -> Action MetaValue,
    ?routingTable :: RoutingTable
  ) =>
  (FilePath -> Action FilePath) ->
  Action Pandoc
makeBookDoc routeChapter = do
  -- Read the table of contents
  toc <- ?getTableOfContents ()

  -- Compose documents for each part
  parts <- for (zip [1 ..] (bookParts toc)) $ \(number, part) -> do
    -- Compose documents for each chapter
    chapters <- for (partChapters part) $ \chapter -> do
      -- Get chapter document
      let chapterSrc = chapterInclude chapter
      (chapterHtml, chapterUrl) <- (,) <$> routeChapter chapterSrc <*> Route.url chapterSrc
      (chapterMetadata, chapterBody) <- getFileWithMetadata chapterHtml
      Pandoc _ chapterBlocks <- Pandoc.markdownToPandoc chapterBody
      -- Get chapter title & ident
      chapterTitle <- failOnError $ chapterMetadata ^. "title"
      let chapterIdent = urlToIdent chapterUrl
      -- Compose chapter document
      let chapterDoc =
            Builder.divWith (chapterIdent, [], [("epub:type", chapterEpubType chapter)]) $
              Builder.header 2 (Builder.text chapterTitle)
                <> Builder.fromList
                  ( chapterBlocks
                      & Pandoc.shiftHeadersBy 1
                      & Pandoc.withIds (qualifyIdent True chapterUrl)
                      & Pandoc.withUrls (qualifyAnchor chapterUrl)
                  )
      return chapterDoc

    -- Compose part document
    let partIdent = Text.pack $ "Part-" <> show @Int number
    let partDoc =
          Builder.divWith (partIdent, [], []) $
            Builder.header 1 (Builder.text (partTitle part))
              <> mconcat chapters
    return partDoc

  -- Get metadata
  defaultMetadata <- ?getDefaultMetadata ()
  title <- failOnError $ defaultMetadata ^. "pagetitle"
  author <- fmap authorName <$> ?getAuthors ()
  rights <- failOnError $ defaultMetadata ^. "license.name"
  date <- failOnError $ defaultMetadata ^. "build_date"

  -- Compose book
  return (Builder.doc (mconcat parts))
    <&> Pandoc.withUrls internalizeUrl
    >>= processCitations
    <&> Pandoc.setMeta "title" (Builder.str title)
    <&> Pandoc.setMeta "author" author
    <&> Pandoc.setMeta "rights" (Builder.str rights)
    <&> Pandoc.setMeta "date" (Builder.str date)

internalizeUrl :: Url -> Url
internalizeUrl url
  | isAbsoluteUrl url = "#" <> qualifyIdent False urlPath hashAndAnchor
  | otherwise = url
  where
    (urlPath, hashAndAnchor) = Text.breakOn "#" url

qualifyAnchor :: Url -> Url -> Url
qualifyAnchor urlPath url
  | "#" `Text.isPrefixOf` url = "#" <> qualifyIdent False urlPath url
  | otherwise = url

qualifyIdent :: Bool -> Url -> Text -> Text
qualifyIdent emptyAnchorMeansNoId urlPath hashAndAnchor
  | Text.null anchor = if emptyAnchorMeansNoId then "" else ident
  | otherwise = ident <> "_" <> anchor
  where
    anchor = Text.dropWhile (== '#') hashAndAnchor
    ident = urlToIdent urlPath

urlToIdent :: Url -> Text
urlToIdent url =
  assert (isNothing $ Text.find (== '#') url) $
    assert (isAbsoluteUrl url) $
      Text.intercalate "-" (filter (not . Text.null) (Text.splitOn "/" (removeIndexHtml url)))

--------------------------------------------------------------------------------
-- Node.js

npmExec :: (HasCallStack, CmdResult r) => [CmdOption] -> String -> [String] -> Action r
npmExec cmdOpts package args = do
  need ["package.json"]
  command (AddEnv "npm_config_yes" "true" : Traced package : Shell : cmdOpts) "npm" ("exec" : package : "--" : args)

sass :: (HasCallStack, CmdResult r) => [CmdOption] -> [String] -> Maybe LazyText.Text -> Action r
sass cmdOpts args maybeStdin = do
  let stdinCmdOpt = [StdinBS (LazyText.encodeUtf8 stdin) | stdin <- maybeToList maybeStdin]
  let stdinArg = ["--stdin" | isJust maybeStdin]
  npmExec (stdinCmdOpt <> cmdOpts) "sass" (stdinArg <> args)

data CmdOutput r where
  OutputToFile :: FilePath -> CmdOutput ()
  OutputToText :: CmdOutput Text

defaultHtmlMinifierArgs :: [String]
defaultHtmlMinifierArgs =
  [ "--collapse-boolean-attributes",
    "--collapse-whitespace",
    "--minify-css",
    "--minify-js",
    "--minify-urls",
    "--quote-character=\\\"",
    "--remove-comments",
    "--remove-empty-attributes",
    "--remove-redundant-attributes",
    "--remove-script-type-attributes",
    "--remove-style-link-type-attributes"
  ]

htmlMinifier :: HasCallStack => CmdOutput r -> [CmdOption] -> [String] -> LazyText.Text -> Action r
htmlMinifier cmdOutput cmdOpts args stdin =
  getMode >>= \case
    Development -> do
      let body = Text.concat $ LazyText.toChunks stdin
      case cmdOutput of
        OutputToFile out -> writeFile' out body
        OutputToText -> return body
    Production -> do
      let stdinCmdOpt = StdinBS (LazyText.encodeUtf8 stdin)
      case cmdOutput of
        OutputToFile out ->
          npmExec (stdinCmdOpt : cmdOpts) "html-minifier" (["--output=" <> out] <> args)
        OutputToText -> do
          Stdout minifiedHtml <- npmExec (stdinCmdOpt : cmdOpts) "html-minifier" args
          return (Text.decodeUtf8 minifiedHtml)

--------------------------------------------------------------------------------
-- HTML5 post-processing
--
-- - removes "/index.html" from URLs
-- - relativizes URLs
-- - adds a default table header scope
-- - minifies HTML using html-minifier

writeHtml5 :: FilePath -> FilePath -> Text -> Action ()
writeHtml5 outDir out html = do
  trackWrite [out]
  genericPostProcessHtml5 (OutputToFile out) outDir out html

postProcessHtml5 :: FilePath -> FilePath -> Text -> Action Text
postProcessHtml5 = genericPostProcessHtml5 OutputToText

genericPostProcessHtml5 :: CmdOutput r -> FilePath -> FilePath -> Text -> Action r
genericPostProcessHtml5 cmdOutput outDir out html = do
  let body =
        html
          & TagSoup.withUrls (removeIndexHtml . relativizeUrl outDir out)
          & TagSoup.addDefaultTableHeaderScope "col"
  let stdin = LazyText.fromChunks [body]
  htmlMinifier cmdOutput [] defaultHtmlMinifierArgs stdin

-- | Convert Markdown to HTML5 using Pandoc.
markdownToHtml5 :: (?getReferences :: () -> Action MetaValue) => Text -> Action Text
markdownToHtml5 = Pandoc.markdownToPandoc >=> processCitations >=> Pandoc.pandocToHtml5

-- | Process Markdown citations with citeproc using the references returned by @?getReferences@.
processCitations :: (?getReferences :: () -> Action MetaValue) => Pandoc -> Action Pandoc
processCitations doc = do
  references <- ?getReferences ()
  Pandoc.processCitations (Pandoc.setMeta "references" references doc)

readerOpts :: ReaderOptions
readerOpts =
  def
    { readerExtensions =
        extensionsFromList
          [ Ext_all_symbols_escapable,
            Ext_auto_identifiers,
            Ext_backtick_code_blocks,
            Ext_citations,
            Ext_footnotes,
            Ext_header_attributes,
            Ext_intraword_underscores,
            Ext_markdown_in_html_blocks,
            Ext_shortcut_reference_links,
            Ext_smart,
            Ext_superscript,
            Ext_subscript,
            Ext_strikeout,
            Ext_task_lists,
            Ext_yaml_metadata_block,
            Ext_raw_html,
            Ext_raw_attribute,
            Ext_fenced_code_blocks,
            Ext_backtick_code_blocks,
            Ext_fenced_divs,
            Ext_bracketed_spans
          ]
    }

writerOpts :: WriterOptions
writerOpts =
  def
    { writerHTMLMathMethod = KaTeX defaultKaTeXURL,
      writerEmailObfuscation = JavascriptObfuscation,
      writerHighlightStyle = Just highlightStyle
    }

highlightStyle :: HighlightStyle
highlightStyle = Pandoc.pygments

highlightCss :: String
highlightCss = Pandoc.styleToCss highlightStyle

--------------------------------------------------------------------------------
-- Agda file info

data RichAgdaFileInfo = RichAgdaFileInfo
  { agdaFileInfo :: Agda.AgdaFileInfo,
    _libraryRawAgdaHtmlDir :: FilePath,
    _rawAgdaHtmlPath :: FilePath,
    _agdaHtmlPath :: FilePath,
    _project :: Project,
    _libraries :: [Agda.Library]
  }
  deriving (Show, Typeable, Eq, Generic, Hashable, Binary, NFData)

pattern AgdaFileInfo ::
  Agda.Library ->
  FilePath ->
  FilePath ->
  Agda.ModuleName ->
  FilePath ->
  FilePath ->
  FilePath ->
  FilePath ->
  FilePath ->
  Project ->
  [Agda.Library] ->
  RichAgdaFileInfo
pattern AgdaFileInfo
  { library,
    libraryIncludePath,
    modulePath,
    moduleName,
    outputFileForLaTeX,
    outputFileForHtml,
    libraryRawAgdaHtmlDir,
    rawAgdaHtmlPath,
    agdaHtmlPath,
    project,
    libraries
  } =
  RichAgdaFileInfo
    ( Agda.AgdaFileInfo
        library
        libraryIncludePath
        modulePath
        moduleName
        outputFileForLaTeX
        outputFileForHtml
      )
    libraryRawAgdaHtmlDir
    rawAgdaHtmlPath
    agdaHtmlPath
    project
    libraries

--------------------------------------------------------------------------------
-- Helper functions

failOnError :: MonadFail m => Either String a -> m a
failOnError = either fail return

failOnNothing :: MonadFail m => String -> Maybe a -> m a
failOnNothing msg = maybe (fail msg) return

ignoreError :: Monoid a => Either String a -> a
ignoreError = fromRight mempty

ignoreNothing :: Monoid a => Maybe a -> a
ignoreNothing = fromMaybe mempty

rightToMaybe :: Either e a -> Maybe a
rightToMaybe = either (const Nothing) Just
