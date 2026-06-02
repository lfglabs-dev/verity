// Single source of truth for "which surface do I write?". Rendered at every
// entry point so the canonical authoring surface (`verity_contract`) is named
// identically everywhere. Pass `children` for an optional page-specific line.
export function CanonicalSurface({ children }: { children?: React.ReactNode }) {
  return (
    <aside className="report-callout">
      <strong>Which surface do I write?</strong>
      <div>
        You author contracts in the <code>verity_contract {'{ … }'}</code> block
        — that is the canonical surface. The <code>Contract</code> monad,{' '}
        <code>_spec</code> predicates, and <code>_meets_spec</code> theorems are
        the <strong>proof layer</strong> beneath it: the compiler lowers{' '}
        <code>verity_contract</code> to that model and the proofs run against it.
        {children ? <> {children}</> : null}
      </div>
    </aside>
  )
}
