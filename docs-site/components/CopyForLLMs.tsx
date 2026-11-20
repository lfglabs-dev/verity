'use client'

import { useCallback, useEffect, useRef, useState } from 'react'
import { CopyIcon, LinkArrowIcon } from 'nextra/icons'
import { ChatGPTLogo, ClaudeLogo, GeminiLogo } from './llm-logos'
import {
  GEMINI_URL,
  buildCompactLlmPrompt,
  buildLlmPrompt,
  chatgptUrl,
  claudeUrl,
  markdownUrlFor,
} from './llm-prompt'

type Status = 'idle' | 'copied' | 'copied-gemini' | 'failed'

async function writeClipboard(text: string): Promise<boolean> {
  try {
    await navigator.clipboard.writeText(text)
    return true
  } catch {
    // Fallback for insecure contexts and older mobile browsers.
    try {
      const ta = document.createElement('textarea')
      ta.value = text
      ta.setAttribute('readonly', '')
      ta.style.position = 'fixed'
      ta.style.opacity = '0'
      document.body.appendChild(ta)
      ta.select()
      const ok = document.execCommand('copy')
      document.body.removeChild(ta)
      return ok
    } catch {
      return false
    }
  }
}

const LABELS: Record<Status, string> = {
  idle: 'Copy for LLMs',
  copied: 'Copied — paste it in your LLM',
  'copied-gemini': 'Copied — paste it in Gemini',
  failed: 'Copy failed',
}

function Chevron({ open }: { open: boolean }) {
  return (
    <svg
      viewBox="0 0 12 12"
      width="12"
      height="12"
      aria-hidden="true"
      focusable="false"
      style={{ transform: open ? 'rotate(180deg)' : undefined, transition: 'transform 120ms ease' }}
    >
      <path d="M2 4.25 6 8l4-3.75" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round" />
    </svg>
  )
}

function Item(props: {
  logo: React.ReactNode
  title: string
  description: string
  external?: boolean
}) {
  return (
    <>
      <span className="verity-copyllm__item-logo">{props.logo}</span>
      <span className="verity-copyllm__item-text">
        <span className="verity-copyllm__item-title">
          {props.title}
          {props.external ? <LinkArrowIcon height="0.9em" aria-hidden="true" /> : null}
        </span>
        <span className="verity-copyllm__item-desc">{props.description}</span>
      </span>
    </>
  )
}

export function CopyForLLMs() {
  const [status, setStatus] = useState<Status>('idle')
  const [open, setOpen] = useState(false)
  const [ctx, setCtx] = useState<{ title: string; pathname: string } | null>(null)
  const root = useRef<HTMLDivElement>(null)
  const menu = useRef<HTMLDivElement>(null)
  const toggle = useRef<HTMLButtonElement>(null)
  const timer = useRef<ReturnType<typeof setTimeout> | null>(null)

  // Page context is read on the client only, so the SSR markup is identical for every page.
  useEffect(() => {
    setCtx({ title: document.title, pathname: window.location.pathname })
  }, [])

  useEffect(() => () => {
    if (timer.current) clearTimeout(timer.current)
  }, [])

  useEffect(() => {
    if (!open) return
    const onDown = (e: MouseEvent | TouchEvent) => {
      if (root.current && !root.current.contains(e.target as Node)) setOpen(false)
    }
    const onKey = (e: KeyboardEvent) => {
      if (e.key === 'Escape') {
        setOpen(false)
        toggle.current?.focus()
      }
    }
    document.addEventListener('mousedown', onDown)
    document.addEventListener('touchstart', onDown)
    document.addEventListener('keydown', onKey)
    return () => {
      document.removeEventListener('mousedown', onDown)
      document.removeEventListener('touchstart', onDown)
      document.removeEventListener('keydown', onKey)
    }
  }, [open])

  const flash = useCallback((next: Status) => {
    setStatus(next)
    if (timer.current) clearTimeout(timer.current)
    timer.current = setTimeout(() => setStatus('idle'), 2400)
  }, [])

  const pageCtx = () => ctx ?? { title: document.title, pathname: window.location.pathname }

  const copyPrompt = useCallback(
    async (success: Status) => {
      const { title, pathname } = pageCtx()
      const ok = await writeClipboard(buildLlmPrompt(title, pathname))
      flash(ok ? success : 'failed')
    },
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [ctx, flash],
  )

  const openGemini = useCallback(async () => {
    setOpen(false)
    // Gemini has no prefill URL: copy the prompt, then open the app to paste it.
    await copyPrompt('copied-gemini')
    window.open(GEMINI_URL, '_blank', 'noopener,noreferrer')
  }, [copyPrompt])

  const onMenuKey = (e: React.KeyboardEvent) => {
    if (e.key !== 'ArrowDown' && e.key !== 'ArrowUp') return
    const items = Array.from(menu.current?.querySelectorAll<HTMLElement>('[role="menuitem"]') ?? [])
    if (!items.length) return
    e.preventDefault()
    const i = items.indexOf(document.activeElement as HTMLElement)
    const next = e.key === 'ArrowDown' ? (i + 1) % items.length : (i - 1 + items.length) % items.length
    items[next].focus()
  }

  const pc = ctx ?? { title: '', pathname: '/' }
  const compact = buildCompactLlmPrompt(pc.title, pc.pathname)

  return (
    <div className="verity-copyllm" ref={root}>
      <div className="verity-copyllm__group">
        <button
          type="button"
          className="verity-copyllm__button"
          onClick={() => copyPrompt('copied')}
          data-state={status}
          title="Copies a prompt that teaches an AI assistant what Verity is and proposes a learning path"
        >
          <span className="verity-copyllm__logos" aria-hidden="true">
            <ClaudeLogo width="18" height="18" />
            <ChatGPTLogo width="18" height="18" />
            <GeminiLogo width="18" height="18" />
          </span>
          <span className="verity-copyllm__label" role="status" aria-live="polite">
            {LABELS[status]}
          </span>
        </button>
        <button
          type="button"
          ref={toggle}
          className="verity-copyllm__toggle"
          aria-haspopup="menu"
          aria-expanded={open}
          aria-label="More ways to use this page with an LLM"
          onClick={() => setOpen((v) => !v)}
        >
          <Chevron open={open} />
        </button>
      </div>

      {open ? (
        <div className="verity-copyllm__menu" role="menu" ref={menu} onKeyDown={onMenuKey}>
          <button
            type="button"
            role="menuitem"
            className="verity-copyllm__item"
            autoFocus
            onClick={() => {
              setOpen(false)
              copyPrompt('copied')
            }}
          >
            <Item
              logo={<CopyIcon width="16" height="16" />}
              title="Copy for LLMs"
              description="Copy a prompt that explains Verity and proposes a learning path"
            />
          </button>
          <a
            role="menuitem"
            className="verity-copyllm__item"
            href={markdownUrlFor(pc.pathname).replace('https://veritylang.com', '')}
            target="_blank"
            rel="noopener noreferrer"
            onClick={() => setOpen(false)}
          >
            <Item
              logo={<span className="verity-copyllm__md" aria-hidden="true">M↓</span>}
              title="View as Markdown"
              description="View this page as plain text"
              external
            />
          </a>
          <a
            role="menuitem"
            className="verity-copyllm__item"
            href={claudeUrl(compact)}
            target="_blank"
            rel="noopener noreferrer"
            onClick={() => setOpen(false)}
          >
            <Item
              logo={<ClaudeLogo width="18" height="18" />}
              title="Open in Claude"
              description="Start a chat with the learning-path prompt"
              external
            />
          </a>
          <a
            role="menuitem"
            className="verity-copyllm__item"
            href={chatgptUrl(compact)}
            target="_blank"
            rel="noopener noreferrer"
            onClick={() => setOpen(false)}
          >
            <Item
              logo={<ChatGPTLogo width="18" height="18" />}
              title="Open in ChatGPT"
              description="Start a chat with the learning-path prompt"
              external
            />
          </a>
          <button type="button" role="menuitem" className="verity-copyllm__item" onClick={openGemini}>
            <Item
              logo={<GeminiLogo width="18" height="18" />}
              title="Open in Gemini"
              description="Copies the prompt, then opens Gemini to paste it"
              external
            />
          </button>
        </div>
      ) : null}
    </div>
  )
}
