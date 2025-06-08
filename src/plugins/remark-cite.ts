import type { Data as MdastData } from "mdast";
import type { Literal } from "unist";
import type { Processor, Transformer } from "unified";
import type { Root as MdastRoot, PhrasingContent, RootContent } from "mdast";
import { citePlugin } from "@benrbray/remark-cite";
import { visit } from "unist-util-visit";
import assert from "assert";

/** Syntax node for text citation. */
export interface TextCiteNode extends Literal {
  type: "text-cite";
  value: string;
  data: MdastData & { key: string; suffix?: string };
}

// Add text citation node to mdast syntax tree:
declare module "mdast" {
  interface PhrasingContentMap {
    textCiteNode: TextCiteNode;
  }
  interface RootContentMap {
    textCiteNode: TextCiteNode;
  }
}

export default function remarkCite(
  this: Processor,
): Transformer<MdastRoot, MdastRoot> {
  // Setup @benrbray's citePlugin:
  citePlugin.call(this);

  // Regular expressions for matching textual citation keys
  const citeRegExp =
    /^(?<before>.*)@(?<key>[A-Za-z0-9]+([:.#$%&-+?<>~\/][A-Za-z0-9]+)*)(\s*\[(?<suffix>[^\]]+)\])?(?<after>.*)$/;

  // Handle textual citations:
  return function (tree) {
    visit(tree, "text", (node, index, parent) => {
      assert(index !== undefined, "expected `index`");
      assert(parent !== undefined, "expected `parent`");
      const match = node.value.match(citeRegExp);
      if (match) {
        const result: RootContent[] | PhrasingContent[] = [];
        const before = match.groups?.before;
        if (before !== undefined) {
          result.push({ type: "text", value: before });
        }
        const key = match.groups?.key;
        if (key) {
          const cite: TextCiteNode = {
            type: "text-cite",
            value: `@${key}`,
            data: { key, suffix: match.groups?.suffix },
          };
          result.push(cite);
        }
        const after = match.groups?.after;
        if (after !== undefined) {
          result.push({ type: "text", value: after });
        }
        parent.children.splice(index, 1, ...result);
      }
    });
  };
}
