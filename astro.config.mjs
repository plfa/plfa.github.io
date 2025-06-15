// @ts-check
/**
 * @typedef {import("mdast-util-to-hast").State} State
 * @typedef {import("mdast").Node} MdastNode
 * @typedef {import("@benrbray/mdast-util-cite").InlineCiteNode} MdastCite
 * @typedef {import("hast").Node} HastNode
 * @typedef {import("hast").Text} HastText
 */
import { defineConfig } from "astro/config";
import remarkBehead from "remark-behead";
import remarkBracketedSpans2 from "remark-bracketed-spans-2";
import remarkCite from "./src/plugins/remark-cite.ts";
import remarkDirective from "remark-directive";
import remarkMath from "remark-math";
import remarkSmartyPants from "remark-smartypants";
import rehypeMathJax from "rehype-mathjax";
import { bracketedSpanToHast } from "mdast-util-bracketed-spans";
import remarkRehypeCite, {
  loadBibTeX,
} from "./src/plugins/remarkRehype-cite.ts";
import remarkTufte from "./src/plugins/remark-tufte.ts";
import remarkRehypeTufte from "./src/plugins/remarkRehype-tufte.ts";
import rehypeTufte from "./src/plugins/rehype-tufte.ts";

// MathJax options:
const MathJax = {
  // TeX Input Processor Options
  // https://docs.mathjax.org/en/latest/options/input/tex.html
  tex: {},
};

// Citation options:
const bibliography = await loadBibTeX("./src/assets/bibliography.bib");

// https://astro.build/config
export default defineConfig({
  site: "https://wen.works",
  base: import.meta.env.DEV ? "" : "/tutorial-template",
  markdown: {
    syntaxHighlight: "prism",
    remarkPlugins: [
      [remarkBehead, { depth: 1 }],
      // @ts-ignore
      remarkBracketedSpans2,
      remarkCite,
      remarkDirective,
      remarkMath,
      // @ts-ignore
      [remarkSmartyPants, { dashes: "oldschool" }],
      remarkTufte,
    ],
    remarkRehype: {
      handlers: {
        bracketedSpan: bracketedSpanToHast,
        ...remarkRehypeCite({ bibliography }),
        ...remarkRehypeTufte(),
      },
    },
    rehypePlugins: [[rehypeMathJax, MathJax], rehypeTufte],
    gfm: true,
  },
});
