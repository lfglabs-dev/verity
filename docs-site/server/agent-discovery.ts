import type { NextResponse } from "next/server";
import { AGENT_DISCOVERY_HEADERS } from "../agent-discovery.mjs";

export function applyAgentDiscoveryHeaders(response: NextResponse): NextResponse {
  for (const { key, value } of AGENT_DISCOVERY_HEADERS) {
    response.headers.set(key, value);
  }

  return response;
}

export function agentDiscoveryHeaderRecord(): Record<string, string> {
  return Object.fromEntries(AGENT_DISCOVERY_HEADERS.map(({ key, value }) => [key, value]));
}
