
module Main where

import Buildfile.Author (Author)
import Buildfile.Contributor (Contributor (..))
import Control.Monad (forM, unless)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.IO.Class (MonadIO)
import Data.Default.Class (Default (def))
import Data.Either (fromRight, isRight)
import Data.Function (on, (&))
import Data.Functor ((<&>))
import Data.List (isPrefixOf, sortBy)
import Data.List qualified as List
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Shoggoth.Agda qualified as Agda
import Shoggoth.CSS.Minify qualified as CSS
import Shoggoth.CSS.Sass (SassOptions (..))
import Shoggoth.CSS.Sass qualified as CSS
import Shoggoth.Configuration (OutputDirectory (..), TemplateDirectory (TemplateDirectory))
import Shoggoth.Metadata
import Shoggoth.PostInfo
import Shoggoth.Prelude
import Shoggoth.Routing
import Shoggoth.TagSoup qualified as TagSoup
import Shoggoth.Template.Pandoc
import Shoggoth.Template.Pandoc.Builder qualified as Builder
import Shoggoth.Template.Pandoc.Citeproc qualified as Citeproc
import Text.Printf (printf)
import GHC.Generics (Generic)
import Data.Hashable


outDir, tmpDir :: FilePath
outDir = "_site"
tmpDir = "_cache"

dataDir, authorDir, contributorDir :: FilePath
dataDir        = "data"
authorDir      = dataDir </> "authors"
contributorDir = dataDir </> "contributors"

bookDir, chapterDir, courseDir, tspl19Dir :: FilePath
bookDir    = "book"
chapterDir = "src"
courseDir  = "courses"
tspl19Dir  = courseDir </> "TSPL/2019"

webDir, assetDir, pagesDir, postDir, styleDir, templateDir :: FilePath
webDir      = "web"
assetDir    = webDir </> "assets"
pagesDir    = webDir </> "pages"
postDir     = webDir </> "posts"
styleDir    = webDir </> "sass"
templateDir = webDir </> "templates"

tmpAgdaHtmlDir, tmpBodyHtmlDir :: FilePath
tmpAgdaHtmlDir = tmpDir </> "stage1" -- Render .lagda.md to .md
tmpBodyHtmlDir = tmpDir </> "stage2" -- Render .md to .html



--------------------------------------------------------------------------------
-- Rules

main :: IO ()
main =
  shakeArgs
    shakeOptions
      { shakeFiles = tmpDir,
        shakeProgress = progressSimple,
        shakeExtra =
          mempty
            & addShakeExtra (OutputDirectory outDir)
            & addShakeExtra (TemplateDirectory templateDir)
            & addShakeExtra readerOpts
            & addShakeExtra writerOpts
      }
    $ do
      --------------------------------------------------------------------------------
      -- Agda libraries

      standardLibrary <- Agda.getStandardLibrary "standard-library"
      -- [standardLibrary, bookLibrary, tspl19Library, postLibrary]

      let getAgdaLibrariesForProject :: Project -> [Agda.Library]
          getAgdaLibrariesForProject project = standardLibrary : localAgdaLibraries
            where
              localAgdaLibraries = getLocalAgdaLibrariesForProject project

      --------------------------------------------------------------------------------
      -- Routing table

      let postOrPermalinkRouter :: FilePath -> Action FilePath
          postOrPermalinkRouter src = case getProject src of
            Right Post -> do
              PostInfo {..} <- either fail return $ parsePostSource (takeFileName src)
              return $ outDir </> postYear </> postMonth </> postDay </> postSlug </> "index.html"
            _ -> permalinkRouter src

      let postOrPermalinkRouterWithAgda :: FilePath -> Action Stages
          postOrPermalinkRouterWithAgda src = do
            let bodyHtml = tmpBodyHtmlDir </> replaceExtensions src "md"
            out <- postOrPermalinkRouter src
            if Agda.isAgdaFile src
              then do
                agdaLibraries <- either fail return $ getAgdaLibrariesForProject <$> getProject src
                (lib, includePath, agdaHtmlFileName) <-
                  either fail return $ Agda.resolveLibraryAndOutputFileName Agda.Html agdaLibraries src
                let agdaHtml = tmpAgdaHtmlDir </> Agda.libraryRoot lib </> includePath </> agdaHtmlFileName
                return $ agdaHtml :> "body_html" :@ bodyHtml :> Output out
              else return $ "body_html" :@ bodyHtml :> Output out

      let ?routingTable =
            mconcat
              [ -- Book
                [chapterDir </> "plfa" <//> "*.md"] *|-> postOrPermalinkRouterWithAgda,
                -- Courses
                [tspl19Dir <//> "*.md"] *|-> postOrPermalinkRouterWithAgda,
                [tspl19Dir <//> "*.pdf"] *|-> \src -> outDir </> makeRelative courseDir src,
                -- Announcements
                [postDir <//> "*.md"] *|-> postOrPermalinkRouterWithAgda,
                -- Assets
                [pagesDir </> "404.md"] |-> permalinkRouter,
                [styleDir </> "style.scss"] |-> outDir </> "assets/css/style.css",
                [assetDir <//> "*"] *|-> \src -> outDir </> "assets" </> makeRelative assetDir src
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
        siteMetadata <- readYaml (dataDir </> "site.yml")
        tocMetadata <- readYaml (dataDir </> "toc.yml")
        authorMetadata <- getAuthors ()
        contributorMetadata <- getContributors ()
        buildDate <- currentDateField rfc822DateFormat "build_date"
        return $
          mconcat
            [ constField "site" (siteMetadata :: Metadata),
              constField "toc" (tocMetadata :: Metadata),
              constField "author" authorMetadata,
              constField "contributor" contributorMetadata,
              buildDate
            ]

      getAgdaLinkFixer <- newCache $ \project -> do
        let localAgdaLibraries = getLocalAgdaLibrariesForProject project
        Agda.makeAgdaLinkFixer (Just standardLibrary) localAgdaLibraries []

      getTemplateFile <- makeCachedTemplateFileGetter
      let ?getTemplateFile = getTemplateFile

      getFileWithMetadata <- newCache $ \cur -> do
        (src, out) <- (,) <$> routeSource cur <*> route cur

        -- Read default metadata:
        defaultMetadata <- getDefaultMetadata ()

        -- Read metadata from source file and body from current file:
        (head, body) <-
          if src == cur
            then do
              readFileWithMetadata src
            else do
              (head, _) <- readFileWithMetadata src
              (_, body) <- readFileWithMetadata cur
              return (head, body)

        -- Source field:
        let sourceField = constField "source" src

        -- Body field:
        let bodyField = constField "body" body

        -- URL field:
        let urlField = constField "url" $ "/" <> makeRelative outDir out

        -- Modified date field (ISO8601):
        modifiedDateField <- lastModifiedISO8601Field src "modified_date"

        -- Post date field (human-readable, optional):
        let dateField = fromRight mempty $ postDateField "%a %-d %b, %Y" src "date"

        -- Post date field (RFC822, optional):
        let dateRfc822Field = fromRight mempty $ postDateField rfc822DateFormat src "date_rfc822"

        let metadata = mconcat [defaultMetadata, head, urlField, bodyField, sourceField, modifiedDateField, dateField, dateRfc822Field]

        return (metadata, body)

      --------------------------------------------------------------------------------
      -- Phony targets

      "build" ~> do
        need [outDir </> "assets/css/highlight.css"]
        need =<< outputs

      "clean" ~> do
        removeFilesAfter tmpDir ["//*"]

      "clobber" ~> do
        removeFilesAfter outDir ["//*"]
        removeFilesAfter tmpDir ["//*"]

      --------------------------------------------------------------------------------
      -- Compile Markdown+Agda to HTML

      -- Stage 1: Compile Agda to HTML
      tmpAgdaHtmlDir <//> "*.md" %> \next -> do
        (src, prev) <- (,) <$> routeSource next <*> routePrev next
        agdaLibraries <- either fail return $ getAgdaLibrariesForProject <$> getProject src
        (lib, includePath, _) <-
          either fail return $ Agda.resolveLibraryAndOutputFileName Agda.Html agdaLibraries src
        let tmpAgdaHtmlDirForLib = tmpAgdaHtmlDir </> Agda.libraryRoot lib </> includePath
        Agda.compileTo Agda.Html agdaLibraries tmpAgdaHtmlDirForLib prev

      -- Stage 2: Compile Markdown to HTML
      tmpBodyHtmlDir <//> "*.md" %> \next -> do
        (src, prev, out) <- (,,) <$> routeSource next <*> routePrev next <*> route next
        maybeAgdaLinkFixer <-
          getProject src
            & either (const Nothing) Just -- rightToMaybe
            & traverse getAgdaLinkFixer
            & fmap (fmap withUrls)
        readFile' prev
          >>= markdownToPandoc
          <&> shiftHeadersBy 2
          <&> fromMaybe id maybeAgdaLinkFixer
          >>= processCitations
          >>= pandocToHtml5
          >>= writeFile' next

      -- Stage 3: Apply HTML templates
      outDir <//> "*.html" %> \out -> do
        (src, prev) <- (,) <$> routeSource out <*> routePrev out
        (metadata, htmlBody) <- getFileWithMetadata prev
        projectHtmlTemplates <-
          either fail return $ getHtmlTemplatesForProject <$> getProject src
        html <- applyTemplates projectHtmlTemplates metadata htmlBody
        writeFile' out $ postProcessHtml5 outDir out html

      --------------------------------------------------------------------------------
      -- Posts

      -- match posts/YYYY-MM-DD-<slug><file-extensions>
      let isPostSource src =
            isRight $
              parsePostSource (makeRelative postDir src)

      -- match _site/YYYY/MM/DD/<slug>/index.html
      let isPostOutput out =
            isRight $
              parsePostOutput (makeRelative outDir out)

      getPostsField <- newCache $ \() -> do
        posts <- filter isPostSource <$> sources
        postsMetadata <- forM posts $ \post -> do
          bodyHtml <- routeAnchor "body_html" post
          (fileMetadata, body) <- getFileWithMetadata bodyHtml
          let bodyHtmlField = constField "body_html" body
          url <- either fail return $ fileMetadata ^. "url"
          htmlTeaserField <- either fail return $ htmlTeaserFieldFromHtml url body "teaser_html"
          textTeaserField <- either fail return $ textTeaserFieldFromHtml body "teaser_plain"
          return $ mconcat [fileMetadata, bodyHtmlField, htmlTeaserField, textTeaserField]
        return $ constField "post" (reverse postsMetadata)

      -- Build /Announcements/
      -- outDir </> "Announcements" </> "index.html" %> \out -> do
      --   src <- routeSource out
      --   postsField <- getPostsField ()
      --   (fileMetadata, indexMarkdownTemplate) <- getFileWithMetadata src
      --   indexMarkdownBody <- applyAsTemplate (postsField <> fileMetadata) indexMarkdownTemplate
      --   indexHtml <-
      --   indexHtml <- applyTemplate "default.html" fileMetadata indexHtmlBody
      --   writeFile' out $ postProcessHtml5 outDir out indexHtml

      -- Build rss.xml
      outDir </> "rss.xml" %> \out -> do
        src <- routeSource out
        postsField <- getPostsField ()
        (fileMetadata, rssXmlTemplate) <- getFileWithMetadata src
        rssXml <- applyAsTemplate (postsField <> fileMetadata) rssXmlTemplate
        writeFile' out rssXml

      --------------------------------------------------------------------------------
      -- Assets

      -- Build 404.html
      outDir </> "404.html" %> \out -> do
        src <- routeSource out
        (fileMetadata, errorMarkdownBody) <- getFileWithMetadata src
        errorDocBody <- markdownToPandoc errorMarkdownBody
        let errorDocBody' = shiftHeadersBy 2 errorDocBody
        errorDocBody'' <- processCitations errorDocBody'
        errorHtmlBody <- pandocToHtml5 errorDocBody''
        errorHtml <- applyTemplates ["default.html"] fileMetadata errorHtmlBody
        writeFile' out $ postProcessHtml5 outDir out errorHtml

      -- Build assets/css/style.css
      outDir </> "assets/css/style.css" %> \out -> do
        src <- routeSource out
        css <- CSS.compileSassWith sassOptions src
        minCss <- CSS.minifyCSS css
        writeFile' out minCss

      -- Build assets/css/highlight.css
      outDir </> "assets/css/highlight.css" %> \out -> do
        let css = Text.pack (styleToCss highlightStyle)
        minCss <- CSS.minifyCSS css
        writeFile' out minCss

      -- Copy course PDFs
      outDir <//> "*.pdf" %> \out -> do
        src <- routeSource out
        copyFile' src out

      -- Copy assets
      outDir </> "assets" <//> "*" %> \out -> do
        src <- routeSource out
        copyFile' src out

--------------------------------------------------------------------------------
-- Agda

data Project
  = Book
  | Course {courseId :: String}
  | Post
  deriving (Show, Eq, Generic)

instance Hashable Project

getProject :: MonadError String m => FilePath -> m Project
getProject src
  | chapterDir `List.isPrefixOf` src = return Book
  | tspl19Dir `List.isPrefixOf` src = return $ Course "tspl19"
  | postDir `List.isPrefixOf` src = return Post
  | otherwise = throwError $ printf "Not in a known Agda project: '%s'" src

getHtmlTemplatesForProject :: Project -> [FilePath]
getHtmlTemplatesForProject Book      = ["page.html", "default.html"]
getHtmlTemplatesForProject Course {} = ["page.html", "default.html"]
getHtmlTemplatesForProject Post      = ["post.html", "default.html"]

getLocalAgdaLibrariesForProject :: Project -> [Agda.Library]
getLocalAgdaLibrariesForProject Book              = [bookLibrary]
getLocalAgdaLibrariesForProject (Course "tspl19") = [bookLibrary, tspl19Library]
getLocalAgdaLibrariesForProject Post              = [bookLibrary, postLibrary]
getLocalAgdaLibrariesForProject (Course courseId) = error $ printf "Unknown course '%s'" courseId

bookLibrary :: Agda.Library
bookLibrary =
  Agda.Library
    { libraryRoot = chapterDir,
      includePaths = ["."],
      canonicalBaseUrl = "https://plfa.github.io/"
    }

tspl19Library :: Agda.Library
tspl19Library =
  Agda.Library
    { libraryRoot = tspl19Dir,
      includePaths = ["."],
      canonicalBaseUrl = "https://plfa.github.io/TSPL/2019/"
    }

postLibrary :: Agda.Library
postLibrary =
  Agda.Library
    { libraryRoot = postDir,
      includePaths = ["."],
      canonicalBaseUrl = "https://plfa.github.io/"
    }

--------------------------------------------------------------------------------
-- Sass Options

sassOptions :: SassOptions
sassOptions =
  def
    { sassIncludePaths = Just [styleDir],
      sassImporters = Just [CSS.minCssImporter styleDir 1]
    }

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
            Ext_backtick_code_blocks
          ]
    }

-- TODO: recover this from the 'readerExtensions' above, or vice versa
markdownFormat :: Text
markdownFormat = "markdown_strict+all_symbols_escapable+auto_identifiers+backtick_code_blocks+citations+footnotes+header_attributes+intraword_underscores+markdown_in_html_blocks+shortcut_reference_links+smart+superscript+subscript+task_lists+yaml_metadata_block+raw_html+raw_attribute+fenced_code_blocks+backtick_code_blocks"

writerOpts :: WriterOptions
writerOpts =
  def
    { writerHTMLMathMethod = KaTeX "",
      writerEmailObfuscation = JavascriptObfuscation,
      writerHighlightStyle = Just highlightStyle
    }

highlightStyle :: HighlightStyle
highlightStyle = pygments