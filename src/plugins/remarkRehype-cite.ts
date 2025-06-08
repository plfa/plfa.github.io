import type { Handler, Handlers, State } from "mdast-util-to-hast";
import type { Parents as MdastParents } from "mdast";
import type {
  CiteItem as InlineCiteItem,
  InlineCiteNode,
} from "@benrbray/mdast-util-cite";
import type { TextCiteNode } from "./remark-cite";
import type { ElementContent as HastElementContent } from "hast";
import type { CSL } from "./remarkRehype-cite-types";
import fs from "fs/promises";
import { fromHtml } from "hast-util-from-html";
import { h } from "hastscript";
import { visit } from "unist-util-visit";

// @ts-ignore
const { Cite, plugins } = await import("@citation-js/core");
// @ts-ignore
await import("@citation-js/plugin-bibtex");
// @ts-ignore
await import("@citation-js/plugin-csl");

/** A parsed bibliography. */
export type Bibliography = CSL[];

/** The options for citation rendering. */
export interface CiteOptions {
  bibliography: Bibliography;
  template?: string;
  lang?: "en-US" | "es-ES" | "de-DE" | "fr-FR" | "nl-NL";
}

export interface CiteItem extends InlineCiteItem {
  authorInText?: boolean;
}

/** Load a CSL file. */
export function loadCsl(template: string, file: string): void {
  plugins.config.get("@csl").templates.add(template, file);
}

/** Load a bibTeX file. */
export async function loadBibTeX(file: string): Promise<Bibliography> {
  const content = await fs.readFile(file, { encoding: "utf-8" });
  return parseBibTeX(content);
}

/** Parse a bibTeX string. */
function parseBibTeX(content: string): Bibliography {
  return new Cite(content).format("data", { format: "object" });
}

/** Format a citation node as a string. */
function formatCiteText(
  citeItems: CiteItem | InlineCiteItem[],
  options: CiteOptions,
): string {
  const cite = new Cite(options.bibliography);
  if (Array.isArray(citeItems)) {
    // TODO: Parse suffix to extract locators.
    const entry = citeItems.map((citation) => ({
      id: citation.key,
      prefix: citation.prefix,
      suffix: citation.suffix,
      "suppress-author": citation.suppressAuthor,
    }));
    return cite.format("citation", { entry, ...options });
  } else {
    // TODO: Parse suffix to extract locators.
    return [
      cite.format("citation", {
        entry: {
          id: citeItems.key,
          "author-only": true,
        },
      }),
      cite.format("citation", {
        entry: {
          id: citeItems.key,
          prefix: citeItems.prefix,
          suffix: citeItems.suffix,
          "suppress-author": true,
        },
      }),
    ].join(" ");
  }
}

/** Format a bibliography a list of HTML entries. */
function formatBibliography(
  citeItems: CiteItem[],
  options: CiteOptions,
): HastElementContent {
  const entry = citeItems.map((citation) => citation.key);
  const cite = new Cite(options.bibliography);
  const htmlEntries: [string, string][] = cite.format("bibliography", {
    format: "html",
    asEntryArray: true,
    entry,
    ...options,
  });
  return h(
    "span",
    { class: "inline-bib" },
    ...htmlEntries.map(([key, html]) => {
      const hast = fromHtml(html, { fragment: true });
      visit(hast, { type: "element", tagName: "div" }, (node) => {
        node.tagName = "span";
        node.properties["data-cite-key"] = key;
        if (!Array.isArray(node.properties.className)) {
          node.properties.className = [];
        }
        node.properties.className.push("inline-bib-entry");
      });
      return hast;
    }),
  );
}

/** Format a citation node as a hast node. */
function formatInlineCiteNode(
  citeItems: CiteItem | InlineCiteItem[],
  options: CiteOptions,
  referenceCollisionMap: Partial<Record<string, number>>,
): HastElementContent[] {
  const text = formatCiteText(citeItems, options);
  const citeItemArray = Array.isArray(citeItems) ? citeItems : [citeItems];
  const reference = citeItemArray.map(({ key }) => key).join("-");
  const referenceCount = (referenceCollisionMap[reference] =
    (referenceCollisionMap?.[reference] ?? 0) + 1);
  const referenceWithCount = `${reference}${referenceCount}`;
  const label = h(
    "label",
    {
      for: referenceWithCount,
      class: ["margin-toggle", "margin-toggle--always-display"],
    },
    h("span", { class: ["margin-toggle--label"] }, text),
  );
  const input = h("input", {
    type: "checkbox",
    id: referenceWithCount,
    class: "margin-toggle",
  });
  const span = h(
    "span",
    {
      class: "marginnote",
    },
    formatBibliography(citeItemArray, options),
  );
  return [label, input, span];
}

export default function remarkRehypeCite(options: CiteOptions): Handlers {
  let referenceCollisionMap: Partial<Record<string, number>> = {};
  return {
    cite: function (
      state: State,
      cite: InlineCiteNode,
      _parent: MdastParents | undefined,
    ): HastElementContent[] {
      const hastNodes = formatInlineCiteNode(
        cite.data.citeItems,
        options,
        referenceCollisionMap,
      );
      hastNodes.forEach((hastNode) => state.patch(cite, hastNode));
      return hastNodes;
    },
    "text-cite": function (
      state: State,
      cite: TextCiteNode,
      _parent: MdastParents | undefined,
    ): HastElementContent[] {
      try {
        const hastNodes = formatInlineCiteNode(
          { ...cite.data, authorInText: true },
          options,
          referenceCollisionMap,
        );
        hastNodes.forEach((hastNode) => state.patch(cite, hastNode));
        return hastNodes;
      } catch (e) {
        return [{ type: "text", value: cite.value }];
      }
    },
  };
}
