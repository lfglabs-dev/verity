import { CopyForLLMs } from './CopyForLLMs'

export function VerityHero() {
  return (
    <section className="verity-hero" aria-labelledby="verity-hero-title">
      <header className="verity-hero__head">
        <p className="verity-kicker">Verity · Machine-checked proofs in Lean 4</p>
        <div className="verity-hero__titlerow">
          <h1 id="verity-hero-title">Verity — formal verification for EVM smart contracts.</h1>
          <CopyForLLMs />
        </div>
        <p className="verity-hero__dek">
          Verity lets you prove your smart contract is correct. You write down what it must do,
          and Lean, a proof checker, confirms it holds for all the inputs you specify.
        </p>
        <nav className="verity-hero__cards" aria-label="Two ways to verify with Verity">
          <a className="verity-hero__card" href="/solidity-import">
            <h2>Import Solidity</h2>
            <p>
              Import supported Solidity functions into Lean and prove properties of the
              resulting model.
            </p>
            <span className="verity-hero__card-cta">
              Start from your Solidity <span aria-hidden="true">→</span>
            </span>
          </a>
          <a className="verity-hero__card" href="/first-contract">
            <h2>Write in Verity</h2>
            <p>
              Write contracts directly in Verity, prove their properties, and compile them
              to EVM bytecode.
            </p>
            <span className="verity-hero__card-cta">
              Start a new contract <span aria-hidden="true">→</span>
            </span>
          </a>
        </nav>
      </header>
    </section>
  )
}
