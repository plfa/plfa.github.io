module Buildfile.Configuration where

import Data.Text (Text)
import Shoggoth.Prelude ((</>))

githubOwner, githubRepo :: Text
githubOwner = "plfa"
githubRepo = "plfa.github.io"

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
