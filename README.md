# Amazing Riemann Hypothesis

An open book, written in Markdown, that gathers the public material on the November 2026 claimed
proofs of the Riemann Hypothesis and organises it into one cited, readable account:

- **Levent Alpöge with Claude** — a Lean-formalized proof of RH and of GRH for Dirichlet L-functions;
- **Alessandro Masullo** — an independent, human-written GRH draft;
- the community work around them: compilations and kernel checks, module guides, errata,
  formalization efforts, expert commentary and press.

**Status: living draft. Neither proof has completed peer review. Nothing here should be read as a verdict.**

## What this book is

**The main line is a textbook.** The chapters in [`chapters/`](chapters/) teach how to understand the
proof: they start from the background a graduate student in analytic number theory already has,
introduce each new idea with motivation and small examples, and then prove it — definition, lemma,
proof, remark — in the order a reader needs, down to the final contradiction. Each step cites the Lean
declaration (file:line, pinned archive hash) or the page of the human source it rests on. Where
Masullo's route differs, it is presented alongside.

Around the main line, the book keeps three records:

1. **Sources** — [`sources/SOURCES.md`](sources/SOURCES.md): every public document, repository,
   thread and article, with version, retrieval date, hash where available, and a paragraph on what it
   contributes.
2. **Contributions** — [`CONTRIBUTIONS.md`](CONTRIBUTIONS.md): who contributed what — the proof
   authors, everyone who compiled, checked, explained, found errata, fixed gaps or formalized parts,
   and our own work — each entry linked to its public record.
3. **Verification** — what has been checked, by whom and how; what is still open.

## Status tags

- **[Lean]** — proved in the pinned Lean archive; declaration cited.
- **[Lean, read]** — and the prose here has been checked against the formal proof.
- **[Paper]** — stated in a human-written source; page cited; not yet tied to Lean.
- **[Community]** — reported by others; link cited; not independently checked by us.
- **[Expository]** — our explanation or heuristic, not a proof.
- **[Open]** — gap, unclear step or disputed point.

(In the narrative chronicle [`chapters/02-the-story-so-far.md`](chapters/02-the-story-so-far.md),
**[Author]** marks statements by Alpöge or Masullo in their own documents or words, and
**[Checked]** marks non-Lean file/metadata/computation checks performed by us with logs in the run
directories.)

## Citation policy

We summarise and explain in our own words and link to the original. Short quotations are marked and
attributed. We do not mirror the Lean archive, the Masullo PDF or other people's notes; we cite them by
URL and hash. Corrections, missing sources and attribution requests are welcome as issues or pull requests.

## Layout

- `chapters/` — the book, one Markdown file per chapter.
- `sources/SOURCES.md` — the annotated bibliography and source map.
- `notes/` — working notes: proof map, outline, open questions.

## Authorship and license

Compiled and written by Hongmin Li with AI assistance (OpenAI Codex / GPT, Anthropic Claude) under the
author's direction. The proofs and the cited works belong to their authors; this book is commentary.

Text: CC BY 4.0. Material quoted from cited works remains under its original license.
