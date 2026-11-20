import { NextResponse } from "next/server";
import { agentDiscoveryHeaderRecord } from "@/server/agent-discovery";

export function GET() {
  return NextResponse.json(
    {
      description: "Verity agent skill index",
      skills: [
        {
          name: "verity",
          url: "/skill.md",
          description:
            "Operational guidance for agents importing Solidity functions, authoring or porting Verity contracts, proving specs, and auditing trust boundaries.",
        },
      ],
    },
    {
      headers: agentDiscoveryHeaderRecord(),
    }
  );
}
