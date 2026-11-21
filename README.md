# The Riemann Hypothesis Proof: An Open Book

A human-readable account of the November 2026 Lean-formalized proof of the Riemann Hypothesis
(and the Dirichlet-character Generalized Riemann Hypothesis) announced by Levent Alpöge with Claude,
read alongside Alessandro Masullo's independent human-written GRH draft.

**Status: working draft. Not peer reviewed. The underlying proof is still being checked by the community.**

## Aim

The Lean archive is ~17 million lines. Machine-checked does not mean understood. This book tries to
explain *why* the proof works, at the level of a graduate student in analytic number theory:

- one coherent narrative from prerequisites to the final contradiction, instead of module-by-module notes;
- every mathematical claim linked to the Lean declaration (file:line, pinned archive hash) that proves it;
- each statement tagged by status — see below;
- where Masullo's route differs, the two arguments are compared side by side.

## Status tags used throughout

- **[Lean]** — proved in the pinned Lean archive; we cite the declaration.
- **[Lean, read]** — and we have read the formal proof and checked the prose explanation matches it.
- **[Paper]** — stated in a human-written source (Alpöge's remark, Masullo's draft), not yet tied to Lean.
- **[Expository]** — our own explanation or heuristic; not a proof.
- **[Open]** — gap, unclear step, or disputed point.

## Sources (pinned)

See `sources/SOURCES.md`. The Lean archive is cited by its sha256; we do not redistribute it.

## Layout

- `chapters/` — the book, one Markdown file per chapter (`00-preface.md`, `01-…`).
- `notes/` — working notes: module maps, dependency graphs, open questions.
- `sources/SOURCES.md` — exact versions, URLs, retrieval dates and hashes.

## Authorship

Written by Hongmin Li with AI assistance (OpenAI Codex / GPT, Anthropic Claude) under the author's direction.
The proof itself is due to its announced authors; this book is commentary. Corrections welcome via issues.

## License

Text: CC BY 4.0. Code snippets quoted from the Lean archive remain under that archive's license.
