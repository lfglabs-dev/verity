import { useMDXComponents as getThemeComponents } from 'nextra-theme-docs'
import { CopyForLLMs } from './components/CopyForLLMs'

const themeComponents = getThemeComponents()
const ThemeH1 = themeComponents.h1 as React.ComponentType<any>

// The "Copy for LLMs" control sits on the same line as the page title: it is rendered
// immediately before the H1 and floats to the end of that line (see .verity-copyllm).
// Home renders it inside the hero's own title row (components/VerityHero.tsx).
function H1(props: Record<string, unknown>) {
  return (
    <>
      <CopyForLLMs />
      <ThemeH1 {...props} />
    </>
  )
}

export function useMDXComponents(components?: Record<string, unknown>) {
  return {
    ...themeComponents,
    h1: H1,
    ...components
  }
}
