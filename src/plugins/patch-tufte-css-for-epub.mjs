#!/usr/bin/env node
/*
 * Rebase font URLs in Tufte CSS for the EPUB.
 */
import CleanCss from "clean-css";
import fs from "fs";
import path from "path";
import url from "url";

const fontUrlPlugin = {
  level1: {
    value: (propertyName, propertyValue) => {
      if (propertyName === "src") {
        const match = /^url\(["'](?<url>.*)["']\)$/.exec(propertyValue);
        const { url } = match?.groups ?? {};
        if (match !== null && url !== undefined) {
          const rebased = path.format(
            Object.assign(path.parse(url), { dir: "../fonts" }),
          );
          propertyValue = `url("${rebased}")`;
        }
      }
      return propertyValue;
    },
  },
};
const cleanCss = new CleanCss({plugins: [fontUrlPlugin]});
const srcFile = url.fileURLToPath(import.meta.resolve("tufte-css/tufte.css"));
const outFile = path.join(path.dirname(srcFile), path.basename(srcFile, '.css') + '.epub.css');
const minData = cleanCss.minify([srcFile]).styles;
const fixData = minData
  .replaceAll(/\bcite\b/g,'span.cite')
  .replaceAll(/\bfooter\b/g,'span.footer');

fs.writeFileSync(outFile, fixData);
