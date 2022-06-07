{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Monad law, left identity" #-}
module Main where

import Buildfile.Author (Author (..))
import Buildfile.Book (Book (..), Part (..), Section (..))
import Buildfile.Contributor (Contributor (..))
import Control.Monad (forM, forM_, unless)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.IO.Class (MonadIO)
import Data.ByteString.Lazy qualified as LazyByteString
import Data.Default.Class (Default (def))
import Data.Either (fromRight, isRight)
import Data.Function (on, (&))
import Data.Functor ((<&>))
import Data.Hashable (Hashable)
import Data.List (isPrefixOf, sortBy)
import Data.List qualified as List
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Traversable (for)
import GHC.Generics (Generic)
import Shoggoth.Agda qualified as Agda
import Shoggoth.CSS.Minify qualified as CSS
import Shoggoth.CSS.Sass (SassOptions (..))
import Shoggoth.CSS.Sass qualified as CSS
import Shoggoth.Configuration (CacheDirectory (..), OutputDirectory (..), TemplateDirectory (..))
import Shoggoth.Metadata
import Shoggoth.PostInfo
import Shoggoth.Prelude
import Shoggoth.Routing
import Shoggoth.TagSoup qualified as TagSoup
import Shoggoth.Template.Pandoc (Extension (..), HTMLMathMethod (..), HighlightStyle, Inlines, Lang, Locale, MetaValue, ObfuscationMethod (..), Pandoc (..), ReaderOptions (..), Reference, WriterOptions (..), extensionsFromList, runPandoc, runPandocWith)
import Shoggoth.Template.Pandoc qualified as Pandoc
import Shoggoth.Template.Pandoc.Builder qualified as Builder
import Shoggoth.Template.Pandoc.Citeproc qualified as Citeproc
import System.Directory (makeAbsolute)
import Text.Printf (printf)

outDir, tmpDir :: FilePath
outDir = "_site"
tmpDir = "_cache"

dataDir, authorDir, contributorDir, legacyDir, bibliographyFile, tableOfContentsFile :: FilePath
dataDir = "data"
authorDir = dataDir </> "authors"
contributorDir = dataDir </> "contributors"
legacyDir = dataDir </> "legacy"
tableOfContentsFile = dataDir </> "tableOfContents.yml"
bibliographyFile = dataDir </> "bibliography.bib"

chapterDir, courseDir :: FilePath
chapterDir = "src"
courseDir = "courses"

epubDir, epubFontsDir, epubStyleDir :: FilePath
epubDir = "epub"
epubFontsDir = epubDir </> "fonts"
epubStyleDir = epubDir </> "sass"

webDir, webAssetDir, webPostDir, webStyleDir, webTemplateDir :: FilePath
webDir = "web"
webAssetDir = webDir </> "assets"
webPostDir = webDir </> "posts"
webStyleDir = webDir </> "sass"
webTemplateDir = webDir </> "templates"

tmpAgdaHtmlDir, tmpBodyHtmlDir, tmpEpubDir :: FilePath
tmpAgdaHtmlDir = tmpDir </> "agda_html" -- Render .lagda.md to .md
tmpBodyHtmlDir = tmpDir </> "body_html" -- Render .md to .html
tmpEpubDir = tmpDir </> "epub"

legacyVersions :: [String]
legacyVersions = ["19.08", "20.07"]

-- TODO:
-- - [ ] build epub
-- - [ ] build pdf

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
      -- Agda libraries

      standardLibrary <- Agda.getStandardLibrary "standard-library"

      let getAgdaLibrariesForProject :: Project -> [Agda.Library]
          getAgdaLibrariesForProject project = standardLibrary : localAgdaLibraries
            where
              localAgdaLibraries = getLocalAgdaLibrariesForProject project

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
                agdaLibraries <-
                  failOnError $
                    getAgdaLibrariesForProject <$> getProject src
                (lib, includePath, agdaHtmlFileName) <-
                  failOnError $
                    Agda.resolveLibraryAndOutputFileName Agda.Html agdaLibraries src
                -- NOTE: Each Agda file compiles to its own directory, i.e., the
                --       `agdaHtmlFileName` is included in the path. Otherwise,
                --       Agda will regenerate files it already generated in a
                --       previous task, and you'll get an error saying that the
                --       temporary file has "changed since being depended upon".
                let agdaHtml = tmpAgdaHtmlDir </> agdaHtmlFileName </> Agda.libraryRoot lib </> includePath </> agdaHtmlFileName
                return $ "agda_html" :@ agdaHtml :> commonStages
              else return commonStages

      let ?routingTable =
            mconcat
              [ -- Book (Web Version)
                ["README.md"] |-> postOrPermalinkRouterWithAgda,
                [webDir </> "TableOfContents.md"] |-> postOrPermalinkRouterWithAgda,
                [chapterDir </> "plfa" <//> "*.md"] *|-> postOrPermalinkRouterWithAgda,
                -- Book (EPUB Version)
                create (outDir </> "plfa.epub"),
                -- Announcements
                [webDir </> "Announcements.md"] |-> postOrPermalinkRouterWithAgda,
                [webDir </> "rss.xml"] |-> outDir </> "rss.xml",
                [webPostDir <//> "*.md"] *|-> postOrPermalinkRouterWithAgda,
                -- Documentation
                [webDir </> "Citing.md"] |-> postOrPermalinkRouterWithAgda,
                [webDir </> "Contributing.md"] |-> postOrPermalinkRouterWithAgda,
                [webDir </> "Notes.md"] |-> postOrPermalinkRouterWithAgda,
                [webDir </> "StyleGuide.md"] |-> postOrPermalinkRouterWithAgda,
                -- Courses
                [courseDir <//> "*.md"] *|-> postOrPermalinkRouterWithAgda,
                [courseDir <//> "*.pdf"] *|-> \src -> outDir </> makeRelative courseDir src,
                -- Assets
                [webDir </> "404.md"] |-> permalinkRouter,
                [webStyleDir </> "style.scss"] |-> outDir </> "assets/css/style.css",
                create (outDir </> "assets/css/highlight.css"),
                [webAssetDir <//> "*"] *|-> \src -> outDir </> "assets" </> makeRelative webAssetDir src,
                -- Versions (Legacy)
                [legacyDir <//> "*"] *|-> \src -> outDir </> makeRelative legacyDir src
              ]

      --------------------------------------------------------------------------------
      -- Caches

      getAuthors <- newCache $ \() -> do
        authorFiles <- getDirectoryFiles authorDir ["*.yml"]
        authors <- traverse (\src -> readYaml $ authorDir </> src) authorFiles
        return (authors :: [Author])

      getContributors <- newCache $ \() -> do
        contributorFiles <- getDirectoryFiles contributorDir ["*.yml"]
        contributors <- traverse (\src -> readYaml $ contributorDir </> src) contributorFiles
        let sortedContributors = sortBy (compare `on` contributorCount) contributors
        return (sortedContributors :: [Contributor])

      getDefaultMetadata <- newCache $ \() -> do
        metadata <- readYaml @Metadata (dataDir </> "metadata.yml")
        authorMetadata <- getAuthors ()
        contributorMetadata <- getContributors ()
        buildDate <- currentDateField rfc822DateFormat "build_date"
        version <- currentDateField "%y.%m" "version"
        return $
          mconcat
            [ metadata,
              constField "author" authorMetadata,
              constField "contributor" contributorMetadata,
              buildDate
            ]
      let ?getDefaultMetadata = getDefaultMetadata

      getReferences <- newCache $ \() -> do
        bibliographyFileBody <- readFile' bibliographyFile
        bibliographyFileDoc@(Pandoc meta _) <- runPandoc $ Pandoc.readBibTeX readerOpts bibliographyFileBody
        case Pandoc.lookupMeta "references" meta of
          Just references -> return references
          Nothing -> fail $ printf "Could not read references from '%s'" bibliographyFile

      let processCitations :: Pandoc -> Action Pandoc
          processCitations doc = do
            references <- getReferences ()
            Pandoc.processCitations $
              Pandoc.setMeta "references" references doc

      getAgdaLinkFixer <- newCache $ \project -> do
        let localAgdaLibraries = getLocalAgdaLibrariesForProject project
        Agda.makeAgdaLinkFixer (Just standardLibrary) localAgdaLibraries []

      getTemplateFile <- Pandoc.makeCachedTemplateFileGetter
      let ?getTemplateFile = getTemplateFile

      --------------------------------------------------------------------------------
      -- Phony targets

      "build" ~> do
        need =<< outputs

      "clean" ~> do
        removeFilesAfter tmpAgdaHtmlDir ["//*"]
        removeFilesAfter tmpBodyHtmlDir ["//*"]
        removeFilesAfter tmpEpubDir ["//*"]

      "clobber" ~> do
        removeFilesAfter tmpAgdaHtmlDir ["//*"]
        removeFilesAfter tmpBodyHtmlDir ["//*"]
        removeFilesAfter tmpEpubDir ["//*"]
        removeFilesAfter outDir ["//*"]

      --------------------------------------------------------------------------------
      -- Table of Contents

      getTableOfContentsField <- newCache $ \() -> do
        tocMetadata <- readYaml tableOfContentsFile
        tocResolved <- resolveIncludes (fmap fst . getFileWithMetadata) tocMetadata
        return $ constField "toc" tocResolved

      -- Build /
      outDir </> "index.html" %> \out -> do
        src <- routeSource out
        tocField <- getTableOfContentsField ()
        (fileMetadata, indexMarkdownTemplate) <- getFileWithMetadata src
        return indexMarkdownTemplate
          >>= Pandoc.applyAsTemplate (tocField <> fileMetadata)
          >>= Pandoc.markdownToPandoc
          >>= processCitations
          >>= Pandoc.pandocToHtml5
          >>= Pandoc.applyTemplates ["page.html", "default.html"] fileMetadata
          <&> postProcessHtml5 outDir out
          >>= writeFile' out

      --------------------------------------------------------------------------------
      -- Compile Markdown & Agda to HTML

      -- Stage 1: Compile Agda to HTML
      tmpAgdaHtmlDir <//> "*.md" %> \next -> do
        (src, prev) <- (,) <$> routeSource next <*> routePrev next
        agdaLibraries <-
          failOnError $
            getAgdaLibrariesForProject <$> getProject src
        (lib, includePath, agdaHtmlFileName) <-
          failOnError $
            Agda.resolveLibraryAndOutputFileName Agda.Html agdaLibraries src
        let tmpAgdaHtmlDirForLib = tmpAgdaHtmlDir </> agdaHtmlFileName </> Agda.libraryRoot lib </> includePath
        Agda.compileTo Agda.Html agdaLibraries tmpAgdaHtmlDirForLib prev

      -- Stage 2: Compile Markdown to HTML
      tmpBodyHtmlDir <//> "*.html" %> \next -> do
        (src, prev, out) <- (,,) <$> routeSource next <*> routePrev next <*> route next
        maybeAgdaLinkFixer <-
          getProject src
            & rightToMaybe
            & traverse getAgdaLinkFixer
            & fmap (fmap Pandoc.withUrls)
        readFile' prev
          >>= Pandoc.markdownToPandoc
          <&> fromMaybe id maybeAgdaLinkFixer
          >>= processCitations
          >>= Pandoc.pandocToHtml5
          >>= writeFile' next

      -- Stage 3: Apply HTML templates
      let hasHtmlBody :: FilePath -> Bool
          hasHtmlBody out = isHtml && not isLegacyVersion
            where
              isHtml =
                (outDir <//> "*.html") ?== out
              isLegacyVersion =
                any (\legacyVersion -> (outDir </> legacyVersion <//> "*") ?== out) legacyVersions

      hasHtmlBody ?> \out -> do
        (src, prev) <- (,) <$> routeSource out <*> routePrev out
        (metadata, htmlBody) <- getFileWithMetadata prev
        let htmlTemplates
              | isPostSource src = ["post.html", "default.html"]
              | otherwise = ["page.html", "default.html"]
        html <- Pandoc.applyTemplates htmlTemplates metadata htmlBody
        writeFile' out $ postProcessHtml5 outDir out html

      --------------------------------------------------------------------------------
      -- Posts

      getPostsField <- newCache $ \() -> do
        posts <- filter isPostSource <$> sources
        postsMetadata <- forM posts $ \post -> do
          bodyHtml <- routeAnchor "body_html" post
          (fileMetadata, body) <- getFileWithMetadata bodyHtml
          let bodyHtmlField = constField "body_html" body
          url <-
            failOnError $
              fileMetadata ^. "url"
          let htmlTeaserField =
                ignoreError $
                  htmlTeaserFieldFromHtml url body "teaser_html"
          let textTeaserField =
                ignoreError $
                  textTeaserFieldFromHtml body "teaser_plain"
          return $ mconcat [fileMetadata, bodyHtmlField, htmlTeaserField, textTeaserField]
        return $ constField "post" (reverse postsMetadata)

      -- Build /Announcements/
      outDir </> "Announcements" </> "index.html" %> \out -> do
        src <- routeSource out
        postsField <- getPostsField ()
        (fileMetadata, indexMarkdownTemplate) <- getFileWithMetadata src
        return indexMarkdownTemplate
          >>= Pandoc.applyAsTemplate (postsField <> fileMetadata)
          >>= Pandoc.markdownToPandoc
          >>= processCitations
          >>= Pandoc.pandocToHtml5
          >>= Pandoc.applyTemplates ["page.html", "default.html"] fileMetadata
          <&> postProcessHtml5 outDir out
          >>= writeFile' out

      -- Build rss.xml
      outDir </> "rss.xml" %> \out -> do
        src <- routeSource out
        postsField <- getPostsField ()
        (fileMetadata, rssXmlTemplate) <- getFileWithMetadata src
        return rssXmlTemplate
          >>= Pandoc.applyAsTemplate (postsField <> fileMetadata)
          >>= writeFile' out

      --------------------------------------------------------------------------------
      -- Assets

      -- Build 404.html
      outDir </> "404.html" %> \out -> do
        src <- routeSource out
        (fileMetadata, errorMarkdownBody) <- getFileWithMetadata src
        return errorMarkdownBody
          >>= Pandoc.markdownToPandoc
          >>= processCitations
          >>= Pandoc.pandocToHtml5
          >>= Pandoc.applyTemplates ["default.html"] fileMetadata
          <&> postProcessHtml5 outDir out
          >>= writeFile' out

      -- Build assets/css/style.css
      outDir </> "assets/css/style.css" %> \out -> do
        src <- routeSource out
        scss <- getDirectoryFiles "" [webStyleDir <//> "*.scss"]
        putInfo $ show scss
        need scss
        CSS.compileSassWith webSassOptions src
          >>= CSS.minifyCSS
          >>= writeFile' out

      -- Build assets/css/highlight.css
      outDir </> "assets/css/highlight.css" %> \out -> do
        return highlightCss
          >>= CSS.minifyCSS
          >>= writeFile' out

      -- Copy static assets
      outDir </> "assets" <//> "*" %> \out -> do
        src <- routeSource out
        copyFile' src out

      -- Copy legacy versions
      --
      -- NOTE: legacy versions are those where the releases on GitHub did not
      --       have relativized URLs, and as such cannot simply be downloaded
      --       into the appropriate version subdirectory without breaking all
      --       links.
      --
      forM_ legacyVersions $ \legacyVersion ->
        outDir </> legacyVersion <//> "*" %> \out -> do
          src <- routeSource out
          copyFile' src out

      -- Copy course PDFs
      --
      -- TODO: build from source instead of copying
      -- TODO: remove PDFs from repository
      --
      outDir <//> "*.pdf" %> \out -> do
        src <- routeSource out
        copyFile' src out

      --------------------------------------------------------------------------------
      -- EPUB

      let routeSection src
            | Agda.isAgdaFile src = routeAnchor "agda_html" src
            | otherwise = return src

      outDir </> "plfa.epub" %> \out -> do
        -- Require metadata and stylesheet
        need
          [ tmpEpubDir </> "epub-metadata.xml",
            tmpEpubDir </> "style.css"
          ]

        -- Read the table of contents
        toc <- readYaml @Book tableOfContentsFile

        -- Compose documents for each part
        parts <- for (zip [1 ..] (bookParts toc)) $ \(number, part) -> do
          --
          -- Compose documents for each section
          sections <- for (partSections part) $ \section -> do
            -- Get section document
            sectionSrc <- routeSection (sectionInclude section)
            (sectionMetadata, sectionBody) <- getFileWithMetadata sectionSrc
            Pandoc _ sectionBlocks <- Pandoc.markdownToPandoc sectionBody

            -- Get section title & ident
            sectionTitle <- failOnError $ sectionMetadata ^. "title"
            let sectionIdent = Text.pack $ takeBaseName sectionSrc

            -- Compose section document
            let sectionDoc =
                  Builder.divWith (sectionIdent, [], [("epub:type", sectionEpubType section)]) $
                    Builder.header 2 (Builder.text sectionTitle)
                      <> Builder.fromList (Pandoc.shiftHeadersBy 1 sectionBlocks)
            return sectionDoc

          -- Compose part document
          let partIdent = Text.pack $ "part-" <> show @Int number
          let partDoc =
                Builder.divWith (partIdent, [], []) $
                  Builder.header 1 (Builder.text (partTitle part))
                    <> mconcat sections
          return partDoc

        -- Get metadata
        defaultMetadata <- getDefaultMetadata ()
        title <- failOnError $ defaultMetadata ^. "pagetitle"
        author <- fmap authorName <$> getAuthors ()
        rights <- failOnError $ defaultMetadata ^. "license.name"

        -- Compose book
        bookDoc <-
          return (Builder.doc (mconcat parts))
            >>= processCitations
            <&> Pandoc.setMeta "title" (Builder.str title)
            <&> Pandoc.setMeta "author" author
            <&> Pandoc.setMeta "rights" (Builder.str rights)
            <&> Pandoc.setMeta "css" [tmpEpubDir </> "style.css"]
            <&> Pandoc.setMeta "highlighting-css" highlightCss

        -- Set writer options
        epubMetadata <- readFile' (tmpEpubDir </> "epub-metadata.xml")
        epubFonts <- getDirectoryFiles "" [epubFontsDir </> "*.ttf"]
        epubTemplate <- Pandoc.compileTemplateFile (epubDir </> "templates" </> "epub.html")

        let writerOptsForEpub =
              writerOpts
                { writerTemplate = Just epubTemplate,
                  writerTableOfContents = True,
                  writerCiteMethod = Pandoc.Natbib,
                  writerWrapText = Pandoc.WrapPreserve,
                  writerTopLevelDivision = Pandoc.TopLevelPart,
                  writerEpubMetadata = Just epubMetadata,
                  writerEpubFonts = epubFonts,
                  writerEpubChapterLevel = 2,
                  writerTOCDepth = 2,
                  writerReferenceLocation = Pandoc.EndOfSection
                }

        epub <- runPandocWith Pandoc.INFO $
          Pandoc.writeEPUB3 writerOptsForEpub bookDoc
        liftIO $ LazyByteString.writeFile out epub

      -- Build epub metadata
      tmpEpubDir </> "epub-metadata.xml" %> \out -> do
        defaultMetadata <- getDefaultMetadata ()
        readFile' (epubDir </> "templates" </> "epub-metadata.xml")
          >>= Pandoc.applyAsTemplate defaultMetadata
          >>= writeFile' out

      -- Build epub stylesheet
      tmpEpubDir </> "style.css" %> \out -> do
        need =<< getDirectoryFiles "" [epubStyleDir <//> "*.scss"]
        CSS.compileSassWith epubSassOptions (epubStyleDir </> "style.scss")
          >>= CSS.minifyCSS
          >>= writeFile' out

--------------------------------------------------------------------------------
-- Agda

data Project
  = Main
  | Course {courseId :: String}
  | Post
  deriving (Show, Eq, Generic)

instance Hashable Project

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

getLocalAgdaLibrariesForProject :: Project -> [Agda.Library]
getLocalAgdaLibrariesForProject Main = [mainLibrary]
getLocalAgdaLibrariesForProject (Course courseId) = [mainLibrary, courseLibrary]
  where
    courseLibrary :: Agda.Library
    courseLibrary =
      Agda.Library
        { libraryRoot = courseDir </> courseId,
          includePaths = ["."],
          canonicalBaseUrl = "https://plfa.github.io/" <> Text.pack courseId
        }
getLocalAgdaLibrariesForProject Post = [mainLibrary, postLibrary]

mainLibrary :: Agda.Library
mainLibrary =
  Agda.Library
    { libraryRoot = chapterDir,
      includePaths = ["."],
      canonicalBaseUrl = "https://plfa.github.io/"
    }

postLibrary :: Agda.Library
postLibrary =
  Agda.Library
    { libraryRoot = webPostDir,
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
-- Sass Options

webSassOptions :: SassOptions
webSassOptions = def {sassIncludePaths = Just [webStyleDir]}

epubSassOptions :: SassOptions
epubSassOptions = def {sassIncludePaths = Just [epubStyleDir]}

--------------------------------------------------------------------------------
-- File reader

getFileWithMetadata ::
  ( ?getDefaultMetadata :: () -> Action Metadata,
    ?routingTable :: RoutingTable
  ) =>
  FilePath ->
  Action (Metadata, Text)
getFileWithMetadata cur = do
  (src, out, url) <- (,,) <$> routeSource cur <*> route cur <*> routeUrl cur

  -- Read default metadata:
  defaultMetadata <- ?getDefaultMetadata ()

  -- Read metadata from source file and body from current file:
  (head, body) <-
    if src == cur
      then do
        readFileWithMetadata src
      else do
        (head, _) <- readFileWithMetadata src
        (_, body) <- readFileWithMetadata cur
        return (head, body)

  -- Title variants:
  let titleVariants =
        ignoreError $
          titleVariantMetadata <$> head ^. "title"

  -- Source field:
  let sourceField = constField "source" src

  -- Body field:
  let bodyField = constField "body" body

  -- URL field:
  let urlField = constField "url" url

  -- Modified date field (ISO8601):
  modifiedDateField <- lastModifiedISO8601Field src "modified_date"

  -- Post date field (human-readable, optional):
  let dateField = fromRight mempty $ postDateField "%a %-d %b, %Y" src "date"

  -- Post date field (RFC822, optional):
  let dateRfc822Field = fromRight mempty $ postDateField rfc822DateFormat src "date_rfc822"

  let metadata =
        mconcat
          [ defaultMetadata,
            head,
            urlField,
            bodyField,
            titleVariants,
            sourceField,
            modifiedDateField,
            dateField,
            dateRfc822Field
          ]

  return (metadata, body)

--------------------------------------------------------------------------------
-- HTML5 post-processing
--
-- - removes "/index.html" from URLs
-- - relativizes URLs
-- - adds a default table header scope

postProcessHtml5 :: FilePath -> FilePath -> Text -> Text
postProcessHtml5 outDir out html5 =
  html5
    & TagSoup.withUrls (removeIndexHtml . relativizeUrl outDir out)
    & TagSoup.addDefaultTableHeaderScope "col"

--------------------------------------------------------------------------------
-- Pandoc options

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

-- TODO: recover this from the 'readerExtensions' above, or vice versa
-- markdownFormat :: Text
-- markdownFormat = "markdown_strict+all_symbols_escapable+auto_identifiers+backtick_code_blocks+citations+footnotes+header_attributes+intraword_underscores+markdown_in_html_blocks+shortcut_reference_links+smart+superscript+subscript+task_lists+yaml_metadata_block+raw_html+raw_attribute+fenced_code_blocks+backtick_code_blocks"

writerOpts :: WriterOptions
writerOpts =
  def
    { writerHTMLMathMethod = KaTeX "",
      writerEmailObfuscation = JavascriptObfuscation,
      writerHighlightStyle = Just highlightStyle
    }

highlightStyle :: HighlightStyle
highlightStyle = Pandoc.pygments

highlightCss :: Text
highlightCss = Text.pack $ Pandoc.styleToCss highlightStyle

--------------------------------------------------------------------------------
-- Helper functions

failOnError :: MonadFail m => Either String a -> m a
failOnError = either fail return

failOnNothing :: MonadFail m => String -> Maybe a -> m a
failOnNothing msg = maybe (fail msg) return

ignoreError :: Monoid a => Either String a -> a
ignoreError = fromRight mempty

rightToMaybe :: Either e a -> Maybe a
rightToMaybe = either (const Nothing) Just
