import { defineCollection, z } from "astro:content";

const reference = defineCollection({
  type: "content",
  schema: z.object({
    title: z.string(),
    order: z.number(),
  }),
});

export const collections = { reference };
