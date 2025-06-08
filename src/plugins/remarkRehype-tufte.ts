import type { Handler, Handlers } from "mdast-util-to-hast";
import type { MarginNoteNode, SideNoteNode } from "./remark-tufte";
import { h } from "hastscript";

export default function remarkRehypeTufte(): Handlers {
  return {
    marginnote: noteToHast,
    sidenote: noteToHast,
  };
}

/**
 * Handler for margin and sidenotes.
 */
export const noteToHast: Handler = (
  state,
  node: MarginNoteNode | SideNoteNode,
  _parent,
) => {
  const result = [];
  // Render the <label> element:
  if (node.type === "sidenote") {
    result.push(
      h("label", {
        for: node.identifier,
        class: ["margin-toggle", "sidenote-number"],
      }),
    );
  }
  if (node.type === "marginnote") {
    if (node.label === undefined) {
      result.push(
        h(
          "label",
          {
            for: node.identifier,
            class: ["margin-toggle"],
          },
          " ⊕",
        ),
      );
    } else {
      result.push(
        h(
          "label",
          {
            for: node.identifier,
            class: ["margin-toggle", "margin-toggle--always-display"],
          },
          h("span", { class: ["margin-toggle--label"] }, node.label),
        ),
      );
    }
  }
  // Render the <input> element
  result.push(
    h("input", {
      type: "checkbox",
      id: node.identifier,
      class: ["margin-toggle"],
    }),
  );
  // Render the <span> element
  result.push(h("span", { class: ["marginnote"] }, ...state.all(node)));
  return result;
};
