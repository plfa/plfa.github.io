{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Monad law, left identity" #-}

module Main where

import Buildfile.Author (Author)
import Buildfile.Contributor (Contributor (..))
import Control.Monad (forM, unless, forM_)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.IO.Class (MonadIO)
import Data.Default.Class (Default (def))
import Data.Either (fromRight, isRight)
import Data.Function (on, (&))
import Data.Functor ((<&>))
import Data.Hashable
import Data.List (isPrefixOf, sortBy)
import Data.List qualified as List
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.Generics (Generic)
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

outDir, tmpDir :: FilePath
outDir = "_site"
tmpDir = "_cache"

dataDir, authorDir, contributorDir, legacyDir :: FilePath
dataDir = "data"
authorDir = dataDir </> "authors"
contributorDir = dataDir </> "contributors"
legacyDir = dataDir </> "legacy"

bookDir, chapterDir, courseDir :: FilePath
bookDir = "book"
chapterDir = "src"
courseDir = "courses"

webDir, assetDir, postDir, styleDir, templateDir :: FilePath
webDir = "web"
assetDir = webDir </> "assets"
postDir = webDir </> "posts"
styleDir = webDir </> "sass"
templateDir = webDir </> "templates"

tmpAgdaHtmlDir, tmpBodyHtmlDir :: FilePath
tmpAgdaHtmlDir = tmpDir </> "agda_html" -- Render .lagda.md to .md
tmpBodyHtmlDir = tmpDir </> "body_html" -- Render .md to .html

legacyVersions :: [String]
legacyVersions = ["19.08", "20.07"]

-- TODO:
-- - [ ] load BibTeX and CSL files as part of processCitations
-- - [ ] include archived versions
-- - [ ] build epub
-- - [ ] build pdf
-- - [ ] set Agda _build directory to be under _cache

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
            if Agda.isAgdaFile src
              then do
                agdaLibraries <-
                  failOnError $
                    getAgdaLibrariesForProject <$> getProject src
                (lib, includePath, agdaHtmlFileName) <-
                  failOnError $
                    Agda.resolveLibraryAndOutputFileName Agda.Html agdaLibraries src
                let agdaHtml = tmpAgdaHtmlDir </> Agda.libraryRoot lib </> includePath </> agdaHtmlFileName
                return $ agdaHtml :> "body_html" :@ bodyHtml :> Output out
              else return $ "body_html" :@ bodyHtml :> Output out

      let ?routingTable =
            mconcat
              [ -- Book (Web Version)
                ["README.md"] |-> postOrPermalinkRouterWithAgda,
                [webDir </> "TableOfContents.md"] |-> postOrPermalinkRouterWithAgda,
                [chapterDir </> "plfa" <//> "*.md"] *|-> postOrPermalinkRouterWithAgda,
                -- Announcements
                [webDir </> "Announcements.md"] |-> postOrPermalinkRouterWithAgda,
                [webDir </> "rss.xml"] |-> outDir </> "rss.xml",
                [postDir <//> "*.md"] *|-> postOrPermalinkRouterWithAgda,
                -- Documentation
                [webDir </> "Citing.md"] |-> postOrPermalinkRouterWithAgda,
                [webDir </> "Contributing.md"] |-> postOrPermalinkRouterWithAgda,
                [webDir </> "StyleGuide.md"] |-> postOrPermalinkRouterWithAgda,
                -- Courses
                [courseDir <//> "*.md"] *|-> postOrPermalinkRouterWithAgda,
                [courseDir <//> "*.pdf"] *|-> \src -> outDir </> makeRelative courseDir src,
                -- Assets
                [webDir </> "404.md"] |-> permalinkRouter,
                [styleDir </> "style.scss"] |-> outDir </> "assets/css/style.css",
                create $ outDir </> "assets/css/highlight.css",
                [assetDir <//> "*"] *|-> \src -> outDir </> "assets" </> makeRelative assetDir src
                -- Versions (Legacy)
                -- [legacyDir <//> "*"] *|-> \src -> outDir </> makeRelative legacyDir src
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
        authorMetadata <- getAuthors ()
        contributorMetadata <- getContributors ()
        buildDate <- currentDateField rfc822DateFormat "build_date"
        return $
          mconcat
            [ constField "site" (siteMetadata :: Metadata),
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
        (src, out, url) <- (,,) <$> routeSource cur <*> route cur <*> routeUrl cur

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
      -- Phony targets

      "build" ~> do
        need =<< outputs

      "clean" ~> do
        removeFilesAfter tmpDir ["//*"]

      "clobber" ~> do
        removeFilesAfter outDir ["//*"]
        removeFilesAfter tmpDir ["//*"]

      --------------------------------------------------------------------------------
      -- Table of Contents

      getTableOfContentsField <- newCache $ \() -> do
        tocMetadata <- readYaml (dataDir </> "toc.yml")
        toc <- flip resolveIncludes tocMetadata $ \chapterSrc -> do
          bodyHtml <- routeAnchor "body_html" chapterSrc
          (metadata, htmlBody) <- getFileWithMetadata bodyHtml
          return $
            mconcat
              [ metadata,
                constField "body_html" htmlBody
              ]
        return $ constField "toc" toc

      -- Build /
      outDir </> "index.html" %> \out -> do
        src <- routeSource out
        tocField <- getTableOfContentsField ()
        (fileMetadata, indexMarkdownTemplate) <- getFileWithMetadata src
        return indexMarkdownTemplate
          >>= applyAsTemplate (tocField <> fileMetadata)
          >>= markdownToPandoc
          >>= processCitations
          >>= pandocToHtml5
          >>= applyTemplates ["page.html", "default.html"] fileMetadata
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
        (lib, includePath, _) <-
          failOnError $
            Agda.resolveLibraryAndOutputFileName Agda.Html agdaLibraries src
        let tmpAgdaHtmlDirForLib = tmpAgdaHtmlDir </> Agda.libraryRoot lib </> includePath
        Agda.compileTo Agda.Html agdaLibraries tmpAgdaHtmlDirForLib prev

      -- Stage 2: Compile Markdown to HTML
      tmpBodyHtmlDir <//> "*.html" %> \next -> do
        (src, prev, out) <- (,,) <$> routeSource next <*> routePrev next <*> route next
        maybeAgdaLinkFixer <-
          getProject src
            & rightToMaybe
            & traverse getAgdaLinkFixer
            & fmap (fmap withUrls)
        readFile' prev
          >>= markdownToPandoc
          <&> fromMaybe id maybeAgdaLinkFixer
          >>= processCitations
          >>= pandocToHtml5
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
        html <- applyTemplates htmlTemplates metadata htmlBody
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
          >>= applyAsTemplate (postsField <> fileMetadata)
          >>= markdownToPandoc
          >>= processCitations
          >>= pandocToHtml5
          >>= applyTemplates ["page.html", "default.html"] fileMetadata
          <&> postProcessHtml5 outDir out
          >>= writeFile' out

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
        errorDocBody' <- processCitations errorDocBody
        errorHtmlBody <- pandocToHtml5 errorDocBody'
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
-- Agda

data Project
  = Book
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
  | chapterDir `List.isPrefixOf` src = return Book
  | courseDir `List.isPrefixOf` src = Course <$> getCourseId src
  | postDir `List.isPrefixOf` src = return Post
  | otherwise = throwError $ printf "Not part of an Agda project: '%s'" src

getLocalAgdaLibrariesForProject :: Project -> [Agda.Library]
getLocalAgdaLibrariesForProject Book = [bookLibrary]
getLocalAgdaLibrariesForProject (Course courseId) = [bookLibrary, courseLibrary]
  where
    courseLibrary :: Agda.Library
    courseLibrary =
      Agda.Library
        { libraryRoot = courseDir </> courseId,
          includePaths = ["."],
          canonicalBaseUrl = "https://plfa.github.io/" <> Text.pack courseId
        }
getLocalAgdaLibrariesForProject Post = [bookLibrary, postLibrary]

bookLibrary :: Agda.Library
bookLibrary =
  Agda.Library
    { libraryRoot = chapterDir,
      includePaths = ["."],
      canonicalBaseUrl = "https://plfa.github.io/"
    }

postLibrary :: Agda.Library
postLibrary =
  Agda.Library
    { libraryRoot = postDir,
      includePaths = ["."],
      canonicalBaseUrl = "https://plfa.github.io/"
    }

--------------------------------------------------------------------------------
-- Posts

-- match posts/YYYY-MM-DD-<slug><file-extensions>
isPostSource :: FilePath -> Bool
isPostSource src = isRight $ parsePostSource (makeRelative postDir src)

-- match _site/YYYY/MM/DD/<slug>/index.html
isPostOutput :: FilePath -> Bool
isPostOutput out = isRight $ parsePostOutput (makeRelative outDir out)

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
            Ext_backtick_code_blocks,
            Ext_fenced_divs,
            Ext_bracketed_spans
            -- header_attributes
            -- inline_code_attributes
            -- link_attributes
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
highlightStyle = pygments

--------------------------------------------------------------------------------
-- Helper functions

failOnError :: MonadFail m => Either String a -> m a
failOnError = either fail return

ignoreError :: Monoid a => Either String a -> a
ignoreError = fromRight mempty

rightToMaybe :: Either e a -> Maybe a
rightToMaybe = either (const Nothing) Just