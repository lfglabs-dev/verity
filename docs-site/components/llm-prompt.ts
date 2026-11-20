/**
 * Prompt copied by the "Copy for LLMs" button.
 *
 * Self-contained on purpose: a chat assistant that cannot browse still gets the
 * mental model, the trust ordering and the learning path. One that can browse
 * is pointed at the raw Markdown sources. Keep every factual line consistent
 * with /guarantees; do not claim more than that page does.
 */

export const SITE = 'https://veritylang.com'

export const ENDING_QUESTION =
  'Do you want to start with a Solidity contract, or vibe-code directly in Verity?'

export function markdownUrlFor(pathname: string): string {
  const clean = pathname.replace(/\/+$/, '')
  return clean === '' ? `${SITE}/index.md` : `${SITE}${clean}.md`
}

export function buildLlmPrompt(pageTitle: string, pathname: string): string {
  const pageUrl = pathname === '/' ? SITE : `${SITE}${pathname}`
  return `You are my guide to Verity (${SITE}), formal verification for EVM smart contracts. I was reading this page: "${pageTitle}" — ${pageUrl}

## How to answer
- Explain in plain language first. Define each term the first time you use it. No jargon walls.
- Be honest about limits. Never claim more than the guarantees below. Say what you actually read versus what you are assuming.
- Keep the first answer short, then guide me one step at a time.

## What Verity is (the short version)
- A test checks some inputs. A proof covers every input allowed by the stated assumptions. Verity lets you state what a contract must always do and have Lean 4, a proof checker, verify it.
- Two equally supported ways to use it:
  1. Import Solidity: import supported Solidity functions into Lean (\`solidity_import\`) and prove properties of the resulting model.
  2. Write in Verity: write the contract directly in Verity, prove properties, and compile to EVM bytecode.
- Manual porting (rewriting an existing Solidity contract by hand as a native Verity contract) is a third, separate thing, not an automatic import.
- Three claims, never to be conflated: (a) imported = the function was modeled without hitting an unsupported construct, nothing is proven yet; (b) proven = a theorem about the model holds under the assumptions stated; (c) certified compiled code = only for contracts written in Verity, and only for the supported fragment. An imported function has no compiler-correctness proof (the report line \`compilerProof unavailable\` is expected, not an error).

## What you are trusting (most to least likely to be the real problem)
1. Your specification. Verity proves the code matches what was written down, not that it was the right thing to write. This is the main risk on both paths.
2. Verity's own pieces. Import path: the importer that translates Solidity into the Lean model (low risk, bugs or gaps stay local to the construct involved). Write-in-Verity path: Verity's compiler, machine-checked for the supported fragment with explicit assumptions (moderate risk).
3. solc and the EVM (very low risk, years of production use). On the import path your deployed bytecode is your normal solc build.
4. Lean's kernel (very low risk, bugs have been found and fixed before but are rare).

## Sources (read these if you can browse, otherwise rely on the summary above)
- This page as Markdown: ${markdownUrlFor(pathname)}
- Agent index: ${SITE}/llms.txt
- Everything concatenated: ${SITE}/llms-full.txt
- Guarantees & limits (read before quoting any guarantee): ${SITE}/guarantees.md

## Suggested learning path
0. Understand the idea: what a proof gives you that a test cannot, and the three claims above.
1. If starting from Solidity: ${SITE}/solidity-import.md — install the pinned solc, select a function, read the import report, state a property, check it in Lean.
2. If starting from scratch: ${SITE}/first-contract.md — storage, function, specification, proof; then ${SITE}/proof-techniques.md.
3. Both: ${SITE}/guarantees.md for what each step does and does not establish; ${SITE}/capabilities.md and ${SITE}/diagnostics.md as references; ${SITE}/agents.md for agent access.

## Your task now
Give me a short, friendly explanation of Verity and the two paths, tailored to the page I was reading. Then end your message with exactly this question and wait for my answer:

${ENDING_QUESTION}

After I answer, walk me through the matching path step by step. Ask before running any command on my machine.`
}

/**
 * Shorter variant for "Open in <assistant>" links, where the prompt travels in a
 * URL query string. The full prompt (above) is what the clipboard gets; this one
 * keeps the task, the sources and the closing question, and tells the assistant
 * to read the sources for the rest.
 */
export function buildCompactLlmPrompt(pageTitle: string, pathname: string): string {
  const pageUrl = pathname === '/' ? SITE : `${SITE}${pathname}`
  return `You are my guide to Verity (${SITE}), formal verification for EVM smart contracts: prove properties of contracts in Lean 4, either by importing supported Solidity functions or by writing contracts directly in Verity. I was reading "${pageTitle}" (${pageUrl}).

Read these first: ${markdownUrlFor(pathname)}, ${SITE}/llms.txt and ${SITE}/guarantees.md. Never claim more than /guarantees does, and say what you read versus what you are assuming. Importing, proving a stated property under assumptions, and certified compiled code are three different claims. Your specification is the main risk; solc, the EVM and Lean's kernel are very low risk.

Explain Verity simply, define each term the first time you use it, and propose a learning path through ${SITE}/solidity-import.md or ${SITE}/first-contract.md, then ${SITE}/guarantees.md. End your message with exactly this question and wait for my answer:

${ENDING_QUESTION}`
}

export const GEMINI_URL = 'https://gemini.google.com/app'

export function claudeUrl(prompt: string): string {
  return `https://claude.ai/new?q=${encodeURIComponent(prompt)}`
}

export function chatgptUrl(prompt: string): string {
  return `https://chatgpt.com/?hints=search&prompt=${encodeURIComponent(prompt)}`
}
