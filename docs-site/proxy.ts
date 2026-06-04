import { NextRequest, NextResponse } from "next/server";
import { applyAgentDiscoveryHeaders } from "@/server/agent-discovery";
import { negotiateContentType } from "@/server/content-negotiation";

/**
 * Known LLM/AI user agent patterns
 * These agents get raw markdown automatically
 */
const LLM_USER_AGENTS = [
  "ChatGPT-User",     // OpenAI ChatGPT browsing
  "GPTBot",           // OpenAI crawler
  "Claude-Web",       // Anthropic (if they add browsing)
  "ClaudeBot",        // Anthropic crawler
  "PerplexityBot",    // Perplexity AI
  "Applebot",         // Apple Intelligence/Siri
  "cohere-ai",        // Cohere
  "anthropic-ai",     // Anthropic
  "Google-Extended",  // Google AI (Bard/Gemini)
  "CCBot",            // Common Crawl (used by many LLMs)
];

/**
 * Check if user agent is an LLM/AI agent
 */
function isLLMUserAgent(userAgent: string | null): boolean {
  if (!userAgent) return false;
  return LLM_USER_AGENTS.some(bot =>
    userAgent.toLowerCase().includes(bot.toLowerCase())
  );
}

function withVaryAccept(response: NextResponse): NextResponse {
  response.headers.set("Vary", "Accept");
  return response;
}

function mentionsNegotiatedAgentType(acceptHeader: string | null): boolean {
  if (!acceptHeader) {
    return false;
  }

  return /\b(text\/markdown|text\/plain|application\/json)\b/i.test(acceptHeader);
}

/**
 * Proxy to serve raw markdown for AI agents
 *
 * Routes to raw markdown API when:
 * 1. URL ends with .md extension (e.g., /setup.md)
 * 2. Accept header includes text/markdown
 * 3. Accept header includes text/plain
 * 4. Query param ?format=md is present
 * 5. User-Agent is a known LLM (ChatGPT, GPTBot, PerplexityBot, etc.)
 *
 * This allows AI agents to fetch documentation as raw markdown
 * while browsers get the rendered HTML version.
 */
export function proxy(request: NextRequest) {
  const { pathname } = request.nextUrl;

  // Skip API routes, static files, and Next.js internals
  if (
    pathname.startsWith("/api/") ||
    pathname.startsWith("/.well-known/") ||
    pathname.startsWith("/_next/") ||
    pathname.startsWith("/static/") ||
    pathname.startsWith("/_pagefind/") ||
    pathname.includes(".") && !pathname.endsWith(".md") // Has extension but not .md
  ) {
    return NextResponse.next();
  }

  const userAgent = request.headers.get("User-Agent");
  const negotiatedType = negotiateContentType(request.headers.get("Accept"));

  // Check if this is a docs page request that wants markdown
  const wantsMarkdown =
    pathname.endsWith(".md") ||
    negotiatedType === "text/markdown" ||
    negotiatedType === "text/plain" ||
    request.nextUrl.searchParams.get("format") === "md" ||
    isLLMUserAgent(userAgent);

  if (wantsMarkdown) {
    // Normalize the path (remove .md extension if present)
    let docPath = pathname.replace(/\.md$/, "");

    // Handle root path
    if (docPath === "" || docPath === "/") {
      docPath = "/index";
    }

    // Preserve query params except format
    const url = new URL(request.url);
    url.pathname = `/api/docs${docPath}`;
    url.searchParams.delete("format");

    // Rewrite to the API route (internal redirect, URL doesn't change for client)
    return withVaryAccept(applyAgentDiscoveryHeaders(NextResponse.rewrite(url)));
  }

  if (
    pathname === "/" &&
    (negotiatedType !== "text/html" ||
      mentionsNegotiatedAgentType(request.headers.get("Accept")))
  ) {
    const url = new URL(request.url);
    url.pathname = "/api/agentgrade/root";
    url.searchParams.set("type", negotiatedType);
    return withVaryAccept(applyAgentDiscoveryHeaders(NextResponse.rewrite(url)));
  }

  if (pathname !== "/" && negotiatedType === "application/json") {
    return withVaryAccept(
      applyAgentDiscoveryHeaders(
        NextResponse.json(
          {
            error: "not_found",
            path: pathname,
          },
          { status: 404 }
        )
      )
    );
  }

  return withVaryAccept(applyAgentDiscoveryHeaders(NextResponse.next()));
}

// Only run proxy on relevant paths
export const config = {
  matcher: [
    /*
     * Match all paths except:
     * - API routes (already handled)
     * - Static files with extensions (images, css, js, etc.)
     * - Next.js internals
     */
    "/((?!api|_next/static|_next/image|_pagefind|favicon.ico|.*\\.[^m][^d]$).*)",
  ],
};
