// "I want to… → start here" router for the three authoring journeys. Mirrors
// the Common-tasks block at the top of llms.txt (the source of truth), so the
// human funnel and the agent funnel point at the same destinations.
const JOURNEYS: { want: string; href: string; start: string }[] = [
  {
    want: 'start a new contract from an idea',
    href: '/first-contract',
    start: 'Your First Contract — storage → function → spec → proof → register.',
  },
  {
    want: 'port an existing Solidity contract',
    href: '/guides/solidity-to-verity',
    start: 'Solidity → Verity — direct mappings, restructuring patterns, a worked port.',
  },
  {
    want: 'prove a contract that already exists',
    href: '/proof-techniques',
    start: 'Proof Techniques — write the `_spec` and the `_meets_spec` theorem.',
  },
]

export function TaskRouter() {
  return (
    <ul className="verity-reading-list" role="list">
      {JOURNEYS.map((j) => (
        <li key={j.href}>
          <a href={j.href} className="verity-reading-list__row">
            <span className="verity-reading-list__title">I want to {j.want}</span>
            <span className="verity-reading-list__note">{j.start}</span>
            <span aria-hidden="true" className="verity-reading-list__arrow">→</span>
          </a>
        </li>
      ))}
    </ul>
  )
}
