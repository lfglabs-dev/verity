import { NextRequest, NextResponse } from "next/server";
import { agentDiscoveryHeaderRecord } from "@/server/agent-discovery";
import { negotiateContentType } from "@/server/content-negotiation";
import { readDoc } from "@/server/docs";

const description =
  "Import selected Solidity functions or author contracts in Verity, state a property, and machine-check the proof in Lean 4.";

const fallbackMarkdown = `# Verity

> ${description}

## Endpoints

- [Import a Solidity function](https://veritylang.com/solidity-import.md) - Automatic Solidity importer quickstart (Markdown).
- [Write contracts in Verity](https://veritylang.com/first-contract) - Native authoring tutorial.
- [Guarantees & limits](https://veritylang.com/guarantees) - What each step establishes and what stays trusted.
- [Documentation](https://veritylang.com/) - Verity overview and guides.
- [API Docs](https://veritylang.com/api/docs/_index) - Machine-readable documentation index.
- [llms.txt](https://veritylang.com/llms.txt) - Agent operating manual.

## Authentication

No authentication is required for public documentation.
`;

const fallbackText = `${description}

Import Solidity quickstart: https://veritylang.com/solidity-import.md
Write contracts in Verity: https://veritylang.com/first-contract
Guarantees & limits: https://veritylang.com/guarantees
Documentation: https://veritylang.com/
Getting started: https://veritylang.com/getting-started
Machine-readable docs index: https://veritylang.com/api/docs/_index
`;

const html = `<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <title>Verity</title>
    <meta name="description" content="${description}">
    <link rel="alternate" type="text/plain" title="llms.txt" href="/llms.txt">
  </head>
  <body>
    <main>
      <h1>Verity</h1>
      <p>${description}</p>
      <p><a href="/llms.txt">llms.txt</a></p>
    </main>
  </body>
</html>
`;

export async function GET(request: NextRequest) {
  const negotiatedType =
    request.nextUrl.searchParams.get("type") ??
    negotiateContentType(request.headers.get("accept"));
  const doc = await readDoc("index");
  const markdown = doc?.markdown ?? fallbackMarkdown;
  const headers = {
    ...agentDiscoveryHeaderRecord(),
    "Vary": "Accept",
    "X-Content-Type-Options": "nosniff",
  };

  if (negotiatedType === "application/json") {
    return NextResponse.json(
      {
        name: "Verity",
        url: "https://veritylang.com/",
        description,
        repository: "https://github.com/lfglabs-dev/verity",
        docs: {
          index: "https://veritylang.com/api/docs/_index",
          llms: "https://veritylang.com/llms.txt",
          full: "https://veritylang.com/llms-full.txt",
        },
      },
      { headers }
    );
  }

  if (negotiatedType === "text/plain") {
    return new NextResponse(fallbackText, {
      headers: {
        ...headers,
        "Content-Type": "text/plain; charset=utf-8",
      },
    });
  }

  if (negotiatedType === "text/html") {
    return new NextResponse(html, {
      headers: {
        ...headers,
        "Content-Type": "text/html; charset=utf-8",
      },
    });
  }

  return new NextResponse(markdown, {
    headers: {
      ...headers,
      "Content-Type": "text/markdown; charset=utf-8",
    },
  });
}
