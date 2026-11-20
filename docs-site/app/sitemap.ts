import type { MetadataRoute } from 'next'

const ROUTES = [
  '',
  // Journeys
  '/solidity-import',
  '/first-contract',
  '/guarantees',
  // Reference & agent access
  '/agents',
  // Introduction
  '/architecture',
  '/trust-model',
  // Setup
  '/getting-started',
  // How-To Guides
  '/guides/add-contract',
  '/guides/solidity-to-verity',
  '/guides/production-solidity-patterns',
  '/guides/linking-libraries',
  '/guides/debugging-proofs',
  // Reference
  '/solidity-import-reference',
  '/examples',
  '/core',
  '/edsl',
  '/edsl/storage',
  '/edsl/computation',
  '/edsl/control-flow',
  '/edsl/functions',
  '/edsl/external-calls',
  '/compiler',
  '/intrinsics',
  '/capabilities',
  '/diagnostics',
  '/verification',
  '/glossary',
  // Explanation
  '/proof-techniques',
  '/faq',
]

export default function sitemap(): MetadataRoute.Sitemap {
  const base = 'https://veritylang.com'
  const lastModified = new Date()
  return ROUTES.map((path) => ({
    url: `${base}${path}`,
    lastModified,
    changeFrequency: path === '' ? 'weekly' : 'monthly',
    priority: path === '' ? 1.0 : 0.7,
  }))
}
