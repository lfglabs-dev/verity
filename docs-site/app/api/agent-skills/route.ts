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
            "Operational guidance for agents adding, porting, proving, and auditing Verity contracts.",
        },
      ],
    },
    {
      headers: agentDiscoveryHeaderRecord(),
    }
  );
}
