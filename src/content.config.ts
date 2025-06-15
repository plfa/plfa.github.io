import { glob } from "astro/loaders";
import { z, defineCollection } from "astro:content";

const content = defineCollection({
  loader: glob({
    pattern: "**/[^_]*.lagda.md",
    base: "./src/content",
    generateId: ({ entry }) => entry.toLowerCase().replace(/(\.[a-z]+)+$/, ""),
  }),
  schema: z.object({
    title: z.string(),
    permalink: z.string(),
  }),
});

export const collections = { content };
