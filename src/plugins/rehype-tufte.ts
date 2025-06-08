import type { Processor, Transformer } from "unified";
import { CONTINUE, visit } from "unist-util-visit";
import type { Root } from "hast";
import assert from "assert";

export default function rehypeTufte(this: Processor): Transformer<Root, Root> {
  return function (tree) {
    // Handle fullwidth directives:
    visit(tree, { type: "element", tagName: "div" }, (div, index, parent) => {
      assert(index !== undefined, "expected `index`");
      assert(parent !== undefined, "expected `parent`");
      const className = div.properties?.className ?? [];
      if (!Array.isArray(className)) return CONTINUE;
      if (!className.includes("fullwidth")) return CONTINUE;
      visit(div, { type: "element", tagName: "figure" }, (figure) => {
        const className =
          figure.properties.className || (figure.properties.className = []);
        if (!Array.isArray(className)) return CONTINUE;
        className.push("fullwidth");
      });
      visit(div, { type: "element", tagName: "pre" }, (pre) => {
        const className =
          pre.properties.className || (pre.properties.className = []);
        if (!Array.isArray(className)) return CONTINUE;
        className.push("fullwidth");
      });
      parent.children.splice(index, 1, ...div.children);
    });
  };
}
