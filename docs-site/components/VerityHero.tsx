export function VerityHero() {
  return (
    <section className="verity-hero" aria-labelledby="verity-hero-title">
      <header className="verity-hero__head">
        <p className="verity-kicker">Verity · Formal verification in Lean 4</p>
        <h1 id="verity-hero-title">Start with your Solidity.</h1>
        <p className="verity-hero__dek">
          Import one function. State what it should do. Let Lean check your proof.
        </p>
        <nav className="verity-hero__cta-row" aria-label="Choose a starting point">
          <a className="verity-hero__cta" href="/solidity-import">
            Import a Solidity function <span aria-hidden="true">→</span>
          </a>
          <a href="/first-contract">Author a new contract in Verity</a>
        </nav>
      </header>
    </section>
  )
}
