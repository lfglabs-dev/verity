import { NextResponse } from "next/server";
import { agentDiscoveryHeaderRecord } from "@/server/agent-discovery";
import { buildAllDocsMarkdown } from "@/server/docs";

export async function GET() {
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
