import { NextRequest, NextResponse } from "next/server";
import { agentDiscoveryHeaderRecord } from "@/server/agent-discovery";
import { buildAllDocsMarkdown, docIndex, readDoc } from "@/server/docs";

/**
 * GET /api/docs/[...slug]
 *
 * Serves raw markdown content for AI agents and programmatic access.
 *
 * Special paths:
 * - /api/docs/_index → List all available docs (JSON)
 * - /api/docs/_all   → All docs concatenated (Markdown)
 *
 * Examples:
 * - /api/docs/index.md → Raw markdown for homepage
 * - /api/docs/compiler → Raw markdown (extension optional)
 */
export async function GET(
  request: NextRequest,
  { params }: { params: Promise<{ slug: string[] }> }
) {
  const { slug } = await params;
  const path = slug.join("/");

  // Special route: list all docs
  if (path === "_index") {
    try {
      return NextResponse.json(
        {
          description: "Verity Documentation Index",
          docs: await docIndex(),
        },
        {
          headers: agentDiscoveryHeaderRecord(),
        }
      );
    } catch {
      return NextResponse.json({ error: "Failed to list docs" }, { status: 500 });
    }
  }

  // Special route: all docs concatenated
  if (path === "_all") {
    try {
      return new NextResponse(await buildAllDocsMarkdown(), {
        headers: {
          ...agentDiscoveryHeaderRecord(),
          "Content-Type": "text/markdown; charset=utf-8",
          "Cache-Control": "public, max-age=3600",
          "X-Content-Type-Options": "nosniff",
        },
      });
    } catch {
      return NextResponse.json({ error: "Failed to compile docs" }, { status: 500 });
    }
  }

  // Regular doc request - normalize path
  let normalizedPath = path.replace(/\.md$/, ""); // Strip .md extension if present

  const doc = await readDoc(normalizedPath);

  if (!doc) {
    return NextResponse.json(
      {
        error: "Document not found",
        path: normalizedPath,
        suggestion: "Use /api/docs/_index to list available documents",
      },
      { status: 404 }
    );
  }

  // Build response with optional metadata header
  const includeMetadata = request.nextUrl.searchParams.get("metadata") === "true";
  let responseContent = doc.markdown;

  if (includeMetadata && (doc.metadata.title || doc.metadata.description)) {
    const metaLines = [];
    if (doc.metadata.title) metaLines.push(`# ${doc.metadata.title}`);
    if (doc.metadata.description) metaLines.push(`> ${doc.metadata.description}`);
    if (metaLines.length) {
      responseContent = metaLines.join("\n") + "\n\n" + doc.markdown;
    }
  }

  return new NextResponse(responseContent, {
    headers: {
      ...agentDiscoveryHeaderRecord(),
      "Content-Type": "text/markdown; charset=utf-8",
      "Cache-Control": "public, max-age=3600",
      "X-Content-Type-Options": "nosniff",
      "X-Doc-Title": doc.metadata.title || normalizedPath,
      "X-Doc-Path": normalizedPath,
    },
  });
}
