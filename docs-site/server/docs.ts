import { readFile, readdir, stat } from "fs/promises";
import { join } from "path";

export const CONTENT_DIR = join(process.cwd(), "content");

export type DocMetadata = Record<string, string>;

export type DocEntry = {
  path: string;
  url: string;
  html_url: string;
  markdown_url: string;
};

export type ResolvedDoc = {
  path: string;
  markdown: string;
  metadata: DocMetadata;
};

export function stripFrontmatter(content: string): string {
  const frontmatterRegex = /^---\s*\n[\s\S]*?\n---\s*\n/;
  return content.replace(frontmatterRegex, "").trim();
}

export function extractFrontmatter(content: string): DocMetadata {
  const match = content.match(/^---\s*\n([\s\S]*?)\n---/);
  if (!match) return {};

  const frontmatter: DocMetadata = {};
  const lines = match[1].split("\n");
  for (const line of lines) {
    const [key, ...valueParts] = line.split(":");
    if (key && valueParts.length) {
      frontmatter[key.trim()] = valueParts.join(":").trim();
    }
  }
  return frontmatter;
}

export async function listDocs(dir: string = CONTENT_DIR, prefix: string = ""): Promise<string[]> {
  const entries = await readdir(dir, { withFileTypes: true });
  const docs: string[] = [];

  for (const entry of entries) {
    if (entry.name.startsWith("_") || entry.name.startsWith(".")) continue;

    const fullPath = join(dir, entry.name);
    const relativePath = prefix ? `${prefix}/${entry.name}` : entry.name;

    if (entry.isDirectory()) {
      docs.push(...(await listDocs(fullPath, relativePath)));
    } else if (entry.name.endsWith(".mdx") || entry.name.endsWith(".md")) {
      docs.push(relativePath.replace(/\.(mdx?|md)$/, ""));
    }
  }

  return docs;
}

export async function docIndex(): Promise<DocEntry[]> {
  const docs = await listDocs();

  return docs.map((doc) => ({
    path: doc,
    url: `/api/docs/${doc}`,
    html_url: `/${doc === "index" ? "" : doc}`,
    markdown_url: `/${doc === "index" ? "index" : doc}.md`,
  }));
}

export async function readDoc(docPath: string): Promise<ResolvedDoc | null> {
  const normalizedPath = docPath.replace(/\.md$/, "");
  const possiblePaths = [
    join(CONTENT_DIR, `${normalizedPath}.mdx`),
    join(CONTENT_DIR, `${normalizedPath}.md`),
    join(CONTENT_DIR, normalizedPath, "index.mdx"),
    join(CONTENT_DIR, normalizedPath, "index.md"),
  ];

  for (const filePath of possiblePaths) {
    try {
      const stats = await stat(filePath);
      if (!stats.isFile()) continue;

      const content = await readFile(filePath, "utf-8");
      return {
        path: normalizedPath,
        markdown: stripFrontmatter(content),
        metadata: extractFrontmatter(content),
      };
    } catch {
      // Try the next candidate path.
    }
  }

  return null;
}

export async function buildAllDocsMarkdown(): Promise<string> {
  const docs = await listDocs();
  const contents: string[] = [
    "# Verity - Complete Documentation",
    "",
    "> Minimal Lean EDSL for Smart Contracts - All documentation concatenated for AI agent consumption.",
    "",
    "---",
    "",
  ];

  for (const docPath of docs) {
    const doc = await readDoc(docPath);
    if (!doc) continue;

    contents.push(`# ${doc.metadata.title || docPath}`);
    contents.push("");
    if (doc.metadata.description) {
      contents.push(`> ${doc.metadata.description}`);
      contents.push("");
    }
    contents.push(doc.markdown);
    contents.push("");
    contents.push("---");
    contents.push("");
  }

  return contents.join("\n");
}
