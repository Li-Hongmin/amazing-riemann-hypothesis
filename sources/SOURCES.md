# Sources: annotated bibliography and source map

Exact versions of everything the book cites. Times are UTC. "Retrieved" means our own download;
sha256 is of the bytes we received. Raw copies and the fetch logs are kept outside the
repository, in the run directory `~/Hermes/state/quota/runs/rhbook-architecture-11211200/`
(`sources/FETCH-LOG.txt`, `fetch_lean_parts.log`, `headers/`); nothing listed here is
redistributed with the book. The summaries below are ours; tags follow the README ([Paper] for
the two human-written mathematical sources, cited by page; [Community] for everything reported
by others, cited by link).

## Source map: what each source contributes

**The Lean archive (Alpöge with Claude).** The primary object of the book: 175,187 Lean 4 files
(Lean v4.33.1, Mathlib v4.33.1) whose top file `src/Main.lean` proves five theorems — Mathlib's
`RiemannHypothesis` and four forms of GRH for Dirichlet L-functions defined in
`src/Statements.lean`. It contains no prose, no license file and no challenge file. Every
[Lean] citation in the book points into it by path and line (Section 1).

**Alpöge's note (`remark.pdf`).** Four pages posted on 2026-11-20 with the links to the archive
(footnote 1, p. 1). It announces the proof, made "working with Claude"; says that the method
also gives GRH and, the author expects, ERH; describes the argument as a descendant of
Stepanov's method in which a chain of theta lifts of length about $\sqrt X$ plays the role of
multiplicity (p. 1); explains why only the Lean code was released, mentioning an informal text
of more than 250,000 pages (p. 2); and lists a dated timeline of the main steps (pp. 3–4). It is
the only human account of the method. Cited as [Paper] with page (Section 2).

**Masullo's draft, *The Music of the Primes*.** A 940-page human-written draft released on
2026-11-20 through Vakil's blog, aiming at GRH for all unitary Hecke characters of all number
fields (p. 6). It builds adelic theta functions and idelic zeta functions (Chapters 2–3),
Schauder bases and Hardy–Sobolev topologies (Chapters 4–9), and a trace formula with a spectral
side (Chapter 10) and a geometric side (Chapter 12), Theorem 12.5.1.1 (p. 519). Chapter 13
(pp. 521–522), where GRH is to be deduced, is still a placeholder; Chapter 14 discusses
multiplicities, function fields and higher rank; Appendices A–E collect background. The
acknowledgements (p. 6) mention known glitches and Brian Conrad's help. Cited as [Paper] with
page (Section 3).

**Vakil's announcement.** Ravi Vakil's blog post of 2026-11-20, which released and hosts
Masullo's PDF. It reports that Conrad has studied the draft closely for months, that his feedback
is being incorporated and that it looks good to him so far, and that the work involves no AI.
[Community] (Section 3).

**The Masullo formalization project (`mccorvie/riemann-masullo`).** A community Lean
formalization of the draft's statements, proceeding in waves through the appendices and
chapters, with an errata log. Its README records that Chapter 13 does not yet state the main
theorem, that doubts about the trace formula raised on the Lean Zulip did not come from the
formalization, and that its own last two target statements are reconstructions not yet
reviewed. [Community] (Section 3).

**Sutherland's verification page.** Andrew Sutherland's (MIT) log of machine checks, run with
Claude Code: compilation of every module, the axiom audit, `leanchecker` replay, the independent
kernels nanoda and con-leche (including con-leche's statement comparison), lean4lean, the status
of the Lean kernels on the export and of `lake comparator`, hashes of every artifact, and an
explicit list of caveats (unsandboxed build; only a 77-module sample compared with `lake build`;
sandboxed-export comparison pending). The most detailed public record of what has been checked.
[Community] (Section 5).

**The LUMI check (`aapolipponen/rh-lean-check-lumi`).** Aapo Lipponen's independent sandboxed
build on the LUMI supercomputer: all modules compile, the hashes of `Main.olean` and
`Statements.olean` match Sutherland's, an axiom and dependency audit of 292 declarations, and the
count that `riemannHypothesis` uses 146,437 of the 175,187 modules. Its `docs/` form a reader's
guide (pages 01–10 and a glossary) edited from AI review reports, with explicit reading-status
markers and a list of what nobody has read. We use it for navigation and cite its findings as
[Community]; we do not reuse its text (Section 5).

**The Comparator setup (`leanprover-community/riemann-hypothesis`, moved from
`Deicyde/riemann-hypothesis`).** A mirror of the archive prepared for Lean's Comparator: a
challenge file stating the five theorems against Mathlib alone, CI, and verification notes that
review the statements, the dependency pins, the kernel fixes included in Lean v4.33.1, a static
scan and the archive's uses of metaprogramming. Its issue tracker holds build improvements and
readers' maps. No Comparator verdict had been posted at our last check. [Community] (Section 5).

**Mathlib at commit `0df444a`.** The eight Mathlib files whose definitions fix the meaning of the
five statements: `riemannZeta` and `RiemannHypothesis`, Dirichlet characters and conductors,
Dirichlet L-functions and their completions, the functional equations, non-vanishing on
$\Re s\ge1$, and the value assigned to $\zeta(1)$. Cited as [Lean] by path and line
(Section 4).

**Buzzard's Xena post (2026-11-12).** Kevin Buzzard's essay on what it means for a claimed proof
to be "checked in Lean", stressing that the first task is to compare the Lean statement with the
intended theorem. Quoted at the start of Chapter 1. [Community] (Section 5).

***Scientific American* (2026-11-20).** Clara Moskowitz's report on the verification effort,
quoting Sutherland's assessment and Buzzard's remark, made on the Lean community's chat server,
that a successful Comparator run was still awaited. Used only for those two quotations.
[Community] (Section 5).

**Literature.** Davenport's and Iwaniec–Kowalski's books are the analytic background the book
assumes; Bombieri's Bourbaki exposé is our reference for Stepanov's method (Chapter 6)
(Section 6).

**Our derived data.** Declaration index, import graph, text scan and citation check, all
reproducible from the archive (Section 7).

# Exact versions

## 1. The Lean archive (primary source)

Author's original parts, `https://alpo.ge/lean.tar.gz.partNN`, NN = 01…14, as linked in
footnote 1 of the announcement. Downloaded 2026-11-21 04:01:46–04:05:21 with `curl`; every part
answered `HTTP/2 200`; the server sent no `Last-Modified` header. (The server also answers 200
with an HTML page for parts that do not exist, so the joined hash below is the real check.)

| Part | Retrieved | Bytes | sha256 | ETag |
|---|---|---:|---|---|
| part01 | 2026-11-21T04:01:46Z | 18000000 | `86974b1c242ca7b6748f3299df4fc64ee0f6e06c776ac964fb64888101a3de77` | `b116580303b65e25529dae6e694a3bab` |
| part02 | 2026-11-21T04:01:59Z | 18000000 | `1c2a2477354a9dfa97ff1ce54861e96ed885bd456fffbaaabc2028314a229c42` | `47a77f2884ae9185547ee36e4c9cf397` |
| part03 | 2026-11-21T04:02:12Z | 18000000 | `1465a23b1b579a881e24e5ffaf7c4c3727af28ea24741f1ec80e1d67947530a3` | `9e114ce09eabe6118621772d21e1813c` |
| part04 | 2026-11-21T04:02:23Z | 18000000 | `3929e327eecb4e2c5c7cae30e104e6a4a52fa6b82d28325bcda8e9da1c86893b` | `edcca56981307792c45f36cf3482c39b` |
| part05 | 2026-11-21T04:02:39Z | 18000000 | `f25d7e80f7c4ad6d674aa18b323ca760f848857c8755501c149317c38a66c75d` | `fe2185367f419c5af1a93a6ca39dd52b` |
| part06 | 2026-11-21T04:02:50Z | 18000000 | `a8c651a68327811b37dce3cca8eda5e0b2102fa227c0d395cbb7553e4dd69939` | `3c430339a285463888abf3979c66353e` |
| part07 | 2026-11-21T04:03:03Z | 18000000 | `65c7e502a9b236a0f68d9e0aa6e089d4c09b9fc7a0960a149384063ccbe5e869` | `0e202b477aa10e6ce56593952cfe9932` |
| part08 | 2026-11-21T04:03:14Z | 18000000 | `71b027ad6e4179c3a50ce72921e3fec0a2dd751ec7472ac2c644ad145a50ec7e` | `687cc9a31b1117665e8d547dfc4d8d78` |
| part09 | 2026-11-21T04:03:31Z | 18000000 | `47718977ebaa8613f1647e93134479780db9320c5fa911463fd312a6257b796f` | `3e707df7cceb335083d5d4b246f7766c` |
| part10 | 2026-11-21T04:03:47Z | 18000000 | `1d85ece78e0779cec26b0cce29c6462d9f90180e56d78120b152df101715240b` | `76ba0730abcd0dc30c763d804e904ded` |
| part11 | 2026-11-21T04:04:01Z | 18000000 | `cf83a159d1a9540012229c376562587dd966da10cd657cbcef53acfd03232448` | `1564eacf9229f51a692673d67aafda05` |
| part12 | 2026-11-21T04:04:55Z | 18000000 | `1aa5415bd2db83b2689afeeb946419303b3c4f599ae790ad74d38465f768b502` | `599c8bfc235b218972f074276126643e` |
| part13 | 2026-11-21T04:05:09Z | 18000000 | `2de4edbce8ebdbfd0b94bc89bab518c7294209f408ec5b14a7be9e4832d9da81` | `004a3be6a80ad529c057d7572be98f8d` |
| part14 | 2026-11-21T04:05:21Z | 5275554 | `53f8ea43a9b5dcab97b84a52f3ac2848711c844a5420a4c56418093bacb3c6f6` | `8a60f30a51ada38b89908f1ab8fcd86c` |

**Joined archive** `lean.tar.gz` (parts concatenated in the order 01…14): 239,275,554 bytes,
sha256 **`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`**, verified
2026-11-21T04:06:03Z. This is the value published by Sutherland's verification page, the LUMI
run and the leanprover-community notes, and the value of our earlier download
(2026-11-21T03:01:59Z, run `rheval-1121/opportunity`).

Pitfall: macOS's `/bin/bash` (3.2) does not zero-pad the brace range `{01..14}`, so
`cat lean.tar.gz.part{01..14}` silently skips parts 01–09 (our first join gave 77,275,554
bytes). Use `for i in $(seq -w 1 14); do cat lean.tar.gz.part$i; done > lean.tar.gz`, or zsh.

Extracted to `lean-archive/lean/` (git-ignored): 175,187 `.lean` files under `src/`,
17,374,215 lines, 1,030,531,854 bytes of source. `lean-toolchain` = `leanprover/lean4:v4.33.1`;
`lakefile.toml` pins Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`;
`lake-manifest.json` pins plausible `b7eb3304`, LeanSearchClient `5f4d51b8`, importGraph
`16f02aa7`, proofwidgets `4be2e3d5`, aesop `3448c0bc`, Qq `92c15be1`, batteries `4488d40d`,
Cli `6130a478`. The archive contains no license file and no challenge file.

## 2. Author's announcement

| Item | URL | Retrieved | Bytes | sha256 |
|---|---|---|---:|---|
| Four-page note | `https://alpo.ge/remark.pdf` | 2026-11-21T04:02:18Z | 245114 | `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d` |
| Home page | `https://alpo.ge/` | 2026-11-21T04:02:15Z; rechecked 04:42:17Z | 11625 | `a7ee08f4821ec5bfdebbc8860730b497b3e252a49fadc14d0d888c9e38a25276` |

Both are byte-identical to our copies of 2026-11-21T02:51Z (run `rheval-1121/opportunity`); no
further write-up had been posted at the recheck. Page references ("remark p. 3") are to the
PDF's four pages.

## 3. Masullo's draft

| Item | URL | Retrieved | Bytes | sha256 |
|---|---|---|---:|---|
| A. M. Masullo, *The Music of the Primes* (940 pp.) | `https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf` | 2026-11-21T04:05:30Z | 6756996 | `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5` |
| R. Vakil, "Hurried Announcement: Alessandro Masullo GRH" (blog post, 2026-11-20) | `https://math216.wordpress.com/2026/11/20/hurried-announcement-alessandro-masullo-grh/` | 2026-11-21T04:05:38Z | 76305 | `35796196c7483539808483fe19962596959e13cb19c2053e0b2aedd461b1828f` |
| Formalization project `mccorvie/riemann-masullo`, README | `https://raw.githubusercontent.com/mccorvie/riemann-masullo/main/README.md` | 2026-11-21T04:05:40Z | 8899 | `69352b475c7a8b58785d2d0e4ae50bb944cf7e7f79d422f8c36e81794e223b9f` |

The PDF is byte-identical to our copy of 2026-11-21T03:01Z. Printed page numbers coincide with
PDF page numbers (checked on pp. 6, 13, 519, 521, 522). The blog page is dynamic; we cite only
the text of the post.

## 4. Mathlib at the pinned commit

All from
`https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/<path>`.

| Path | Retrieved | Bytes | sha256 |
|---|---|---:|---|
| `Mathlib/NumberTheory/LSeries/RiemannZeta.lean` | 2026-11-21T04:02:31Z | 12306 | `db9f37f08bcce379c502549f604c0e98bf4a39b3a3440606861bbac847f2a1a9` |
| `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean` | 2026-11-21T04:10:40Z | 18979 | `86d3aaad83e64cb64a24167fd4ddb2eeec5ca4a19a9298459e87a57fec151040` |
| `Mathlib/NumberTheory/DirichletCharacter/Basic.lean` | 2026-11-21T04:10:41Z | 26329 | `f004670a9bedc23c4dfaeb61b90d5e613a6b604f9486640eb1ce4ae3699ef64e` |
| `Mathlib/NumberTheory/LSeries/ZMod.lean` | 2026-11-21T04:10:42Z | 28254 | `8b65bc72be88177c735a919cc1deba62d62397796dfb9eae24e6609e24212ea3` |
| `Mathlib/NumberTheory/LSeries/HurwitzZeta.lean` | 2026-11-21T04:10:42Z | 8543 | `181fcf0d1e92ef1d38d1fccecf313d814b6511913aee8e6c4f2d720d0cb5220d` |
| `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` | 2026-11-21T04:10:43Z | 21780 | `945a2fd23ca9ebd2d48f101d771ef9117dd9847d48fd77ea2623d8c345f4f5a9` |
| `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean` | 2026-11-21T04:13:24Z | 32972 | `3eb3f0864a28c7085e7f37917e50e024e5dfa2073821e3324b3873f050dfed89` |
| `Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean` | 2026-11-21T04:30:15Z | 39471 | `db0a44702615c879abb084e3d950085f0f9b3fd71fddbf57105ad4d9cfea92e8` |

## 5. Verification reports and community guides

| Item | URL | Retrieved | Bytes | sha256 | Version read |
|---|---|---|---:|---|---|
| A. Sutherland, "Verification files for the Lean proof of the Riemann Hypothesis" | `https://math.mit.edu/~drew/grh/` | 2026-11-21T04:02:13Z; rechecked 04:42:14Z (identical) | 12782 | `de7153ec1b22acab193a99824d427d41050e2c0d2c4374ec518d52fc0de62307` | "Page last updated 2026-11-20 22:05 UTC"; identical to our copy of 02:51Z |
| LUMI independent check (A. Lipponen), README | `https://raw.githubusercontent.com/aapolipponen/rh-lean-check-lumi/main/README.md` | 2026-11-21T04:02:26Z | 9064 | `4a51000fb1a6d43a22f8a4e26a160ffe6ef22e50646a18ac92ff9cc8e237789c` | repository head `82d91dbbd04d` (2026-11-20T23:56:59Z), unchanged at 04:42:16Z |
| LUMI reader's guide, `docs/README.md` | `…/rh-lean-check-lumi/main/docs/README.md` | 2026-11-21T04:02:57Z | 14124 | `b34663b4fa5484c87bd3b0be4a08308a114fe84fdc0661fd787ac252bda9495f` | docs added in `40e1ae43477a` (2026-11-20T22:40:20Z) |
| LUMI `docs/01-what-is-proved.md` | `…/docs/01-what-is-proved.md` | 2026-11-21T04:03:00Z | 13830 | `37eaf1cc6340053aa2edfa283d400361035b243f96f324e60d79a441660e603c` | |
| LUMI `docs/02-proof-map.md` | `…/docs/02-proof-map.md` | 2026-11-21T04:03:01Z | 21884 | `49aff9f68fcbbf7fd09d2231c040373679df2a82429c67fc72fa50d7cd303402` | |
| LUMI `docs/03-analytic-endgame.md` | `…/docs/03-analytic-endgame.md` | 2026-11-21T04:03:04Z | 19563 | `6cb255aadc9f50dde387456bab85a68f72c7daec4903bcef1baa42a5bdc5ebec` | |
| LUMI `docs/04-chain-and-one-half.md` | `…/docs/04-chain-and-one-half.md` | 2026-11-21T04:03:05Z | 31832 | `3650ba3e36082f3fa104357e992c3b4e544be2537d21c6819606008492c7afda` | |
| LUMI `docs/05-galois-representations.md` | `…/docs/05-galois-representations.md` | 2026-11-21T04:03:07Z | 21177 | `dc304e6a40d4f6233e8fa22feb1bfbb34a9b7f7c42be732f88c9f884a50b94a6` | |
| LUMI `docs/06-window-bound.md` | `…/docs/06-window-bound.md` | 2026-11-21T04:03:09Z | 20315 | `927a2874edca7eae6eb412de85bdf41b6e180f9fbf09e1bebfaa5cc1207f8ef0` | |
| LUMI `docs/07-named-theorems.md` | `…/docs/07-named-theorems.md` | 2026-11-21T04:03:11Z | 43596 | `27e9ac7e6b837cb098c6e288154c88a210e29297e91c22cc4f2cde38a84f3f20` | |
| LUMI `docs/08-archive-anatomy.md` | `…/docs/08-archive-anatomy.md` | 2026-11-21T04:03:13Z | 13011 | `05cae3471ef9c699fb03df4684518e918f18e285fde3bd2208045b98aaed44d4` | |
| LUMI `docs/09-building-and-checking.md` | `…/docs/09-building-and-checking.md` | 2026-11-21T04:03:15Z | 9952 | `baf959527315bb4be5ac868386d54c10cecfe33b3138b797c6e9207748d88a6c` | |
| LUMI `docs/10-open-frontier.md` | `…/docs/10-open-frontier.md` | 2026-11-21T04:03:17Z | 23552 | `14355d0d8d621789a7688a354f1fe2c86567b54d8645259cfb1a792cf7c7ccc1` | |
| LUMI `docs/glossary.md` | `…/docs/glossary.md` | 2026-11-21T04:03:19Z | 21761 | `60be9375373e6487d77ee3e0b18a2501617c1b8b62fc84da3f5de5fbeb95d555` | |
| LUMI `docs/reports/` (skeleton, vacuity-check, theta-chain, analytic-core, core-gm, literature, static-reachability) | `…/docs/reports/<name>.md` | 2026-11-21T04:03:20–04:03:28Z | — | see `FETCH-LOG.txt` | |
| LUMI `results/build-summary.json` | `…/rh-lean-check-lumi/main/results/build-summary.json` | 2026-11-21T04:23:06Z | 453 | `a2763844491a03287ecdbfe5868d71146a7d8ed22a70695b95bf7c12091fe072` | |
| LUMI `results/static-scan.txt` | `…/rh-lean-check-lumi/main/results/static-scan.txt` | 2026-11-21T04:23:07Z | 7128 | `d8c54329b1c86ba8eea4e2a0c9a89a252a253470d20c5da610387952d065d425` | |
| Comparator setup `leanprover-community/riemann-hypothesis` (moved from `Deicyde/riemann-hypothesis`), README | `https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/main/README.md` | 2026-11-21T04:02:24Z | 3575 | `e2ea5fa16f37c8d4509c517ca808dcf5babe8f4b0308ff33d3888e6c6a8fb34d` | head `371a1a26d5e1` (02:23:57Z) at retrieval; head `4286c9ca372a` (04:27:41Z, build-cache infrastructure) at the 04:42:15Z recheck |
| Comparator setup, `verification/NOTES.md` | `https://raw.githubusercontent.com/Deicyde/riemann-hypothesis/main/verification/NOTES.md` (redirects to the leanprover-community repository) | 2026-11-21T04:02:19Z | 15489 | `a0b67cd13f99bb2c6de9a3ff569716f44fe732abaf31fe013a07434fb5dfcf2b` | includes the correction made after issue #2 |
| Comparator setup, `src/Challenge.lean` | `https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/main/src/Challenge.lean` | 2026-11-21T04:23:07Z | 1222 | `a3cebbf30be6b9268a0ed413c9bbc256dfa9f4bfa04f1a75f144d135da5e21a5` | lines 3–16 byte-identical to the archive's `src/Statements.lean` lines 3–16 |
| Comparator setup, issue list | `https://api.github.com/repos/leanprover-community/riemann-hypothesis/issues?state=all&per_page=50` | 2026-11-21T04:42:17Z | 85066 | `b55903bce5d5e61222d2c9754ed260f7567ed336ae361fda4811f5ad7c1abc31` | issues #1–#10; no Comparator result posted |
| K. Buzzard, "…and the proof is checked in Lean", Xena blog, 2026-11-12 | `https://xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/` | 2026-11-21T04:23:04Z | 131922 | `b404e77b8472ae2f8e75a16bccdf8425bc875ba3777b222865d9f7802c5509e3` | quoted in Chapter 1 |
| C. Moskowitz, "The AI Riemann hypothesis proof is almost certainly true, independent mathematicians attest", *Scientific American*, 2026-11-20 | `https://www.scientificamerican.com/article/the-ai-riemann-hypothesis-proof-is-almost-certainly-true-independent-mathematicians-attest/` | 2026-11-21T04:23:05Z | 137656 | `f44ac91b93cc0ae1526e94a040a01821248c68649154baf694b899f83354a103` | quotes of Sutherland and Buzzard |

Consulted but not cited as evidence: T. Tao's blog post of 2026-11-20
(`https://terrytao.wordpress.com/2026/11/20/unforced-euler-singularity-unforced-navier-stokes-singularity-and-the-generalized-riemann-hypothesis/`,
retrieved 04:05:41Z, sha256 `28d6e810bd49e899bb653b0876336a90f56ee26248e39716e4b330e0b921d9e2`);
*Science* (`science.org`, HTTP 403, not read); the Lean Zulip threads (login required, not read;
cited only through the reports above).

## 6. Literature

Bibliographic data checked online on 2026-11-21.

- H. Davenport, *Multiplicative Number Theory*, 3rd ed., revised by H. L. Montgomery, Graduate
  Texts in Mathematics 74, Springer, New York, 2000, ISBN 978-0-387-95097-6.
- H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004,
  ISBN 978-0-8218-3633-0, doi:10.1090/coll/053.
- E. Bombieri, "Counting points on curves over finite fields (d'après S. A. Stepanov)",
  Séminaire Bourbaki, 25e année (1972/73), exp. no. 430, in Lecture Notes in Math. 383,
  Springer, 1974, pp. 234–241, doi:10.1007/BFb0057311; open copy at
  `https://www.numdam.org/item/SB_1972-1973__15__234_0/`.

## 7. Our own derived data (not in the repository)

In the run directory: `index/decls.tsv.gz` (1,057,807 declaration headers with file:line),
`index/imports.tsv.gz`, `index/files.tsv.gz`, `index/import_cones.json` (built by
`build_index.py`); `static_scan.json` (by `static_scan.py`); `kexactB_family_files.txt` (72 files);
`citations_report.txt` (by `check_citations.py`, a machine check of every file:line citation in
`chapters/` and `notes/` against the extracted archive and the Mathlib files above). See
`notes/proof-map.md`, "Reproducibility".
