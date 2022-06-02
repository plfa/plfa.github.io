module Main where

import Control.Monad (forM, unless)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.IO.Class (MonadIO)
import Data.Default.Class (Default (def))
import Data.Either (fromRight, isRight)
import Data.Function ((&), on)
import Data.Functor ((<&>))
import Data.List (isPrefixOf, sortBy)
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
import Buildfile.Author (Author)
import Buildfile.Contributor (Contributor (..))

outDir, tmpDir :: FilePath
outDir = "_site"
tmpDir = "_cache"

authorDir, contributorDir :: FilePath
authorDir         = "authors"
contributorDir    = "contributors"

postSrcDir :: FilePath
postSrcDir = "posts"

tmpAgdaHtmlDir, tmpBodyHtmlDir :: FilePath
tmpAgdaHtmlDir = tmpDir </> "stage1" -- Render .lagda.md to .md
tmpBodyHtmlDir = tmpDir </> "stage2" -- Render .md to .html

styleSrcDir, styleOutDir :: FilePath
styleSrcDir = "sass"
styleOutDir = outDir </> "assets/css"

highlightStyle :: HighlightStyle
highlightStyle = pygments

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
            & addShakeExtra (TemplateDirectory "templates")
            & addShakeExtra
              def
                { readerExtensions = pandocExtensions
                }
            & addShakeExtra
              def
                { writerHTMLMathMethod = KaTeX "",
                  writerEmailObfuscation = JavascriptObfuscation,
                  writerHighlightStyle = Just highlightStyle
                }
      }
    $ do
      --------------------------------------------------------------------------------
      -- Agda libraries

      standardLibrary <- Agda.getStandardLibrary "standard-library"
      let agdaLibraries = [standardLibrary, plfaLibrary, tspl19Library, postLibrary]

      --------------------------------------------------------------------------------
      -- Routing table

      -- let postRouter :: FilePath -> Either String Stages
      --     postRouter src = do
      --       PostInfo {..} <- parsePostSource (takeFileName src)
      --       let postBodyHtml = tmpBodyHtmlDir </> replaceExtensions src "md"
      --       let postOut = outDir </> postYear </> postMonth </> postDay </> postSlug </> "index.html"
      --       if Agda.isAgdaFile src
      --         then do
      --           postAgdaHtml <- Agda.htmlOutputPath tmpAgdaHtmlDir agdaLibraries src
      --           return $ postAgdaHtml :> "body_html" :@ postBodyHtml :> Output postOut
      --         else return $ "body_html" :@ postBodyHtml :> Output postOut

      let ?routingTable =
            mconcat
              [ -- Assets
                ["pages/404.md"] |-> permalinkRouter,
                ["sass/style.scss"] |-> outDir </> "assets/css/style.css",
                ["assets//*"] *|-> \src -> outDir </> src
              ]

      --------------------------------------------------------------------------------
      -- Caches

      getAuthors <- newCache $ \() -> do
        authorFiles <- getDirectoryFiles authorDir ["*.yml"]
        authors <- traverse readYaml authorFiles
        return (authors :: [Author])

      getContributors <- newCache $ \() -> do
        contributorFiles <- getDirectoryFiles contributorDir ["*.yml"]
        contributors <- traverse readYaml contributorFiles
        let sortedContributors = sortBy (compare `on` contributorCount) contributors
        return (sortedContributors :: [Contributor])

      getDefaultMetadata <- newCache $ \() -> do
        siteMetadata <- readYaml "src/site.yml"
        tocMetadata <- readYaml "src/toc.yml"
        publishedDate <- currentDateField rfc822DateFormat "build_date"
        authorMetadata <- getAuthors ()
        contributorMetadata <- getContributors ()
        return $ mconcat
          [ constField "site" (siteMetadata :: Metadata)
          , constField "toc" (tocMetadata :: Metadata)
          , constField "author" authorMetadata
          , constField "contributor" contributorMetadata
          , publishedDate
          ]

      getAgdaLinkFixer <- newCache $ \() ->
        Agda.makeAgdaLinkFixer (Just standardLibrary) [plfaLibrary, tspl19Library, postLibrary] []

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
      -- Posts

      -- match posts/YYYY-MM-DD-<slug><file-extensions>
      -- let isPostSource src = isRight $
      --       parsePostSource (makeRelative postSrcDir src)

      -- match _site/YYYY/MM/DD/<slug>/index.html
      -- let isPostOutput out = isRight $
      --       parsePostOutput (makeRelative outDir out)

      -- getPostsField <- newCache $ \() -> do
      --   posts <- filter isPostSource <$> sources
      --   postsMetadata <- forM posts $ \post -> do
      --     bodyHtml <- routeAnchor "body_html" post
      --     (fileMetadata, body) <- getFileWithMetadata bodyHtml
      --     let bodyHtmlField = constField "body_html" body
      --     url <- either fail return $ fileMetadata ^. "url"
      --     htmlTeaserField <- either fail return $ htmlTeaserFieldFromHtml url body "teaser_html"
      --     textTeaserField <- either fail return $ textTeaserFieldFromHtml body "teaser_plain"
      --     return $ mconcat [fileMetadata, bodyHtmlField, htmlTeaserField, textTeaserField]
      --   return $ constField "post" (reverse postsMetadata)

      -- Build index.hmtl
      -- outDir </> "index.html" %> \out -> do
      --   src <- routeSource out
      --   postsField <- getPostsField ()
      --   (fileMetadata, indexHtmlTemplate) <- getFileWithMetadata src
      --   indexHtmlBody <- applyAsTemplate (postsField <> fileMetadata) indexHtmlTemplate
      --   indexHtml <- applyTemplate "default.html" fileMetadata indexHtmlBody
      --   writeFile' out $ postProcessHtml5 outDir out indexHtml

      -- Build rss.xml
      -- outDir </> "rss.xml" %> \out -> do
      --   src <- routeSource out
      --   postsField <- getPostsField ()
      --   (fileMetadata, rssXmlTemplate) <- getFileWithMetadata src
      --   rssXml <- applyAsTemplate (postsField <> fileMetadata) rssXmlTemplate
      --   writeFile' out rssXml

      -- Stage 1: Compile Agda to HTML
      -- tmpAgdaHtmlDir <//> "*.md" %> \next -> do
      --   prev <- routePrev next
      --   Agda.compileTo Agda.Html agdaLibraries tmpAgdaHtmlDir prev

      -- Stage 2: Compile Markdown to HTML
      -- tmpBodyHtmlDir <//> "*.md" %> \next -> do
      --   (out, prev, src) <- (,,) <$> route next <*> routePrev next <*> routeSource next
      --   agdaLinkFixer <- getAgdaLinkFixer ()
      --   let maybeAgdaLinkFixer
      --         | Agda.isAgdaFile src = Just (withUrls agdaLinkFixer)
      --         | otherwise = Nothing
      --   readFile' prev
      --     >>= markdownToPandoc
      --     <&> shiftHeadersBy 2
      --     <&> fromMaybe id maybeAgdaLinkFixer
      --     >>= processCitations
      --     >>= pandocToHtml5
      --     >>= writeFile' next

      -- Stage 3: Apply templates
      -- isPostOutput ?> \out -> do
      --   (prev, src) <- (,) <$> routePrev out <*> routeSource out
      --   (metadata, postHtmlBody) <- getFileWithMetadata prev
      --   return postHtmlBody
      --     >>= applyTemplates ["post.html", "default.html"] metadata
      --     <&> postProcessHtml5 outDir out
      --     >>= writeFile' out

      --------------------------------------------------------------------------------
      -- Assets

      -- alternatives $ do
      --   -- Build 404.html
      --   outDir </> "404.html" %> \out -> do
      --     src <- routeSource out
      --     (fileMetadata, errorHtmlBody) <- getFileWithMetadata src
      --     errorHtml <- applyTemplate "default.html" fileMetadata errorHtmlBody
      --     writeFile' out $ postProcessHtml5 outDir out errorHtml

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

      -- Copy assets/
      outDir </> "assets" <//> "*" %> \out -> do
        src <- routeSource out
        copyFile' src out

--------------------------------------------------------------------------------
-- Agda

plfaSrcDir :: FilePath
plfaSrcDir = "src"

plfaLibrary :: Agda.Library
plfaLibrary =
  Agda.Library
    { libraryRoot = "",
      includePaths = ["src"],
      canonicalBaseUrl = "https://plfa.github.io/"
    }

tspl19Library :: Agda.Library
tspl19Library =
  Agda.Library
    { libraryRoot = "courses/tspl/2019",
      includePaths = [""],
      canonicalBaseUrl = "https://plfa.github.io/TSPL/2019/"
    }

postLibrary :: Agda.Library
postLibrary =
  Agda.Library
    { libraryRoot = "",
      includePaths = [postSrcDir],
      canonicalBaseUrl = "https://wen.works/"
    }

--------------------------------------------------------------------------------
-- Sass Options

sassOptions :: SassOptions
sassOptions =
  def
    { sassIncludePaths = Just [styleSrcDir],
      sassImporters = Just [CSS.minCssImporter styleSrcDir 1]
    }

--------------------------------------------------------------------------------
-- HTML5 post-processing
--
-- * removes "/index.html" from URLs
-- * relativizes URLs

postProcessHtml5 :: FilePath -> FilePath -> Text -> Text
postProcessHtml5 outDir out html5 =
  html5
    & TagSoup.withUrls (removeIndexHtml . relativizeUrl outDir out)
    & TagSoup.addDefaultTableHeaderScope "col"

