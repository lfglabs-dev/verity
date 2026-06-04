export const AGENT_DISCOVERY_LINKS = [
  '</llms.txt>; rel="llms-txt"',
  '</llms-full.txt>; rel="llms-full-txt"',
  '</skill.md>; rel="agent-skill"',
].join(", ");

export const AGENT_DISCOVERY_HEADERS = [
  { key: "Link", value: AGENT_DISCOVERY_LINKS },
  { key: "Vary", value: "Accept" },
  { key: "X-Llms-Txt", value: "/llms.txt" },
  { key: "X-Llms-Full-Txt", value: "/llms-full.txt" },
  { key: "X-Agent-Skill", value: "/skill.md" },
];

export const AGENT_DISCOVERY_REWRITES = [
  { source: "/.well-known/llms.txt", destination: "/llms.txt" },
  { source: "/.well-known/llms-full.txt", destination: "/llms-full.txt" },
  { source: "/.well-known/skill.md", destination: "/skill.md" },
  { source: "/.well-known/agent-skills", destination: "/api/agent-skills" },
];
