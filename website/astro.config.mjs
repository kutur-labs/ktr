// @ts-check
import { defineConfig } from 'astro/config';
import tailwindcss from '@tailwindcss/vite';
import { transformerNotationDiff, transformerNotationHighlight } from '@shikijs/transformers'
// @ts-ignore
import fs from 'node:fs';
import vercel from '@astrojs/vercel';

// Custom ktr language grammar and themes for Shiki
const ktrGrammar = JSON.parse(fs.readFileSync('./src/shiki/ktr.tmLanguage.json', 'utf-8'));
const ktrDarkTheme = JSON.parse(fs.readFileSync('./src/shiki/ktr-dark.json', 'utf-8'));
const ktrLightTheme = JSON.parse(fs.readFileSync('./src/shiki/ktr-light.json', 'utf-8'));

// https://astro.build/config
export default defineConfig({
  output: 'static', // Pre-render all pages at build time
  markdown: {
    shikiConfig: {
      themes: {
        dark: ktrDarkTheme,
        light: ktrLightTheme
      },
      langs: [ktrGrammar],
      transformers: [
        {
          line(node, line) {
            node.properties['data-line'] = line;
          }
        },
        transformerNotationDiff(),
        transformerNotationHighlight()
      ]
    }
  },
  vite: {
    plugins: [tailwindcss()]
  },
  adapter: vercel()
});