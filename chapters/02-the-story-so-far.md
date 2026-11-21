# Chapter 2. The story so far

*A dated record of the first seventeen hours, from the posting of Alpöge's note on 20 November 2026 to
05:57 UTC on 21 November. It narrates who claimed, reported and checked what, and in which order.
It is not a verdict: Chapter 1 discusses what the formal statement says, §1.6 tabulates the machine
checks, and the later chapters planned in `notes/outline.md` discuss the mathematics of both proofs.*

## 2.0 How to read this chapter

Every factual sentence carries one of three provenance markers, followed by the source.

| Marker | Meaning | Example |
|---|---|---|
| **[Author]** | What Levent Alpöge or Alessandro Maria Masullo say about their own work, in their own documents or in their own words as quoted by others. When the source is the note or the draft, cited by page, this is the README's [Paper]. | [Author · A1, p. 2] |
| **[Community]** | What anyone else reports: checkers, forum posts, repositories, commentators, the press. Not checked by us (README tag). | [Community · V1] |
| **[Checked]** | What we checked ourselves, with the method stated. The logs are in the run directories named in `sources/SOURCES.md`. | [Checked · V12] |

[Open] marks a point that is unresolved, and [Lean, read] refers to our own reading of the archive in
Chapter 1. Source IDs (A1, V2, …) are entries of the annotated bibliography, `sources/SOURCES.md`,
Part II. Lean Zulip messages are cited as "V2 #id" (the thread on Alpöge's proof) or "V3 #id" (the
thread on Masullo's draft); each is at
`https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/<topic>/near/<id>`.

All times are UTC, and the date is 20 November 2026 unless stated. Times have three kinds of
precision. Server timestamps (Zulip messages, Git commits, GitHub issues, X post ids) are exact.
Publication times of articles are what the outlet's page metadata says. Creation times of PDFs are
what the file's metadata records, which the author's software sets; we report them as recorded and
do not treat them as proof of when a file was written.

Quotations are short and marked; everything else is our paraphrase.

## 2.1 Before the announcement

The last page of Alpöge's note lists twenty steps, the earliest dated 6 October
2026 and the last "11/16/26: GRH" [Author · A1, pp. 3–4]. The note says that this "rough timeline"
was provided by Claude after a search, and warns that where Claude was the expert the descriptions
paraphrase an AI summary "which might make zero sense" [Author · A1, p. 3 and fn. 4]. The decisive
moment is placed "late Sunday night", that is, the night of 15 November, after which he "messaged
Dario" about announcing [Author · A1, p. 2]. The press identifies Dario as Anthropic's chief
executive, Dario Amodei [Community · P15], and *Quanta* reports that Alpöge obtained the result on
Monday 16 November and held it for several days [Community · P17].

On 12 November Kevin Buzzard published an essay
on what it means for a proof to be "checked in Lean", insisting that the first task is to compare
the Lean statement with the intended theorem [Community · C2]; it predates the claim and does not
mention it [Checked · C2: publication date of the post]. In August, Anthropic had reported that an
unreleased Claude model raised the proven proportion of zeros of ζ on the critical line from 41.6%
to 67.2%, with the paper examined by Brian Conrey and Dan Goldston, and had written: "We don’t
expect that the techniques Claude used will lead to proving the Riemann hypothesis" [Community · A6].

The acknowledgements of Masullo's draft date the start of the work to his
first graduate year at Stanford, where Conrad was his advisor, and say it "took nearly 12 years to
assemble" [Author · A4, p. 6]. They mention excerpts from a letter to Peter Sarnak sent in mid-October
2026, a four-and-a-half-hour discussion with Sarnak at the IAS on the Sunday before the release, and
arrangements by Conrad and Vakil "for me to return to Stanford for a year to finish the polishing
of the paper" [Author · A4, p. 6]. Vakil later wrote that Conrad "has been looking closely at it for
months" [Community · A5].

## 2.2 The announcement (12:52–14:50)

The PDF of Alpöge's note records its creation at 12:52:48 [Checked · A1: PDF metadata]. The note
is four pages long and is posted on Alpöge's personal domain, whose home page does not link it
[Checked · A1, A3]. Its central sentence reads: "I believe I have, working with Claude, discovered a
proof of the Riemann Hypothesis" [Author · A1, p. 1]. It adds that the method also resolves "the
so-called Generalized Riemann Hypothesis", that he expects the Extended Riemann Hypothesis "with
more time", and that "Claude and I have also formalized the arguments without assumptions"
[Author · A1, p. 1]. Footnote 1 gives the fourteen URLs of the Lean archive [Author · A1, p. 1].

The note calls the timing "horrible", says "There is an
obvious cynical view, to do with the timing, but it is false", and states that, because posting an
unreadable informal text would be inappropriate, he "decided to only present Lean" [Author · A1,
p. 2]. The informal text, in a footnote, "hit 250,000+ pages" [Author · A1, p. 2, fn. 2]. He intends
"to write it properly" and expects the argument to be "massively simplified" [Author · A1, p. 1].

What the archive proves is narrower than "GRH" in its usual sense: its five final theorems are
Mathlib's `RiemannHypothesis` and four statements about Dirichlet L-functions; Hecke L-functions
of other number fields are not covered [Lean, read · Chapter 1, §§1.3–1.4].

The first public signal we found is a post on X by Scott Armstrong at 13:41:10, a screenshot of the
note with the words "@__alpoge__ ftw" [Community · C7]. *Quanta* reports that Armstrong posted it
because Tristan Buckmaster had sent it to him [Community · P17]. At 13:58:06 Jack McCarthy opened
the Lean Zulip thread "Discussion: Alpöge Proves the Riemann Hypothesis": the note had been
"uploaded less than an hour ago" with "no formal announcement yet", and he was compiling the code
"on two separate devservers" [Community · V2 #642224678]. *Scientific American* published its first
article with a timestamp of 14:00 [Community · P1].

Riccardo Brasca reported
compiling "in a sandbox" at 14:12 [Community · V2 #642229032, #642229062], noted at 14:23 that the
archive ships no challenge file importing only Mathlib [Community · V2 #642232248], and named the
independent checkers nanoda and con-leche at 14:32 [Community · V2 #642234870]. To a question about
exploiting a kernel bug, Buzzard answered at 14:35 that this "would have to find bugs in several
independently-written kernels including at least one which is formally verified" [Community · V2
#642235897].

The repository `TomasOrtega/RH`, with the extracted code, was created at
14:16:39 [Community · G8]. Jack McCarthy, as GitHub user Deicyde, committed a byte-exact mirror at
14:36:09 ("Mirror the submission exactly as published") and created the repository that became the
Comparator setup at 14:47:49 [Community · V5]. The Internet Archive captured the note at 14:19:58
and the first and last archive parts at 14:20:02–14:20:03 [Checked · V12]. The archived bytes of
these three files equal the files we downloaded the next morning, so every later check concerns the
files posted that afternoon [Checked · A1, A2, V12: SHA-1 of our copies against the archive's
digests]. The fourteen parts join to sha256 `9631b4f0…49c7fc` [Checked · A2; Part I, §1].

## 2.3 First builds (14:50–19:10)

Kevin Weil reposted Armstrong's post at 15:18:05 [Community · C7]. *New
Scientist* published at 15:20, quoting Buzzard: "Let’s see if it compiles first" [Community · P2].
Thomas Bloom pointed readers to the Zulip thread at 15:29:43 [Community · C7]. At 15:18 Chris
Birkbeck posted a high-level overview of the proof "that fable has given me", an AI summary placing
the burden on bounds for Selmer- or Ш-type groups in a family of fields [Community · G4]. At 16:30
Bartosz Naskręcki wrote that there was not yet "full confirmation from the paranoid-mode comparator
test" [Community · C7]. *The Verge* published at 16:34 [Community · P3].

Andrew Sutherland's compilation of all 175,187 modules finished with zero errors at 16:43:21
[Community · V1]. At 16:53 he wrote that he had compiled the code and was running Comparator on the
Deicyde setup [Community · V2 #642277030]. At 16:55 he confirmed the archive hash, said he had used
"8x192 core machines" and that it "took just over an hour", and noted that the summary he posted came
from "Fable 5.2 which orchestrated the computation" [Community · V2 #642277830]. At 17:05 he warned
that Comparator is single-threaded and would take "several hours" [Community · V2 #642281156].
*Quanta* describes his compile as the first, finished "shortly before noon" Eastern time
[Community · P17].

Le Figaro published at 17:10 and Der Spiegel at 17:30
[Community · P27, P28]. Terence Tao posted at 17:19 that Alpöge, "using an internal AI model, has
generated an (enormous) Lean-only proof of the Generalized Riemann Hypothesis", pointed to the
Zulip thread as "probably the best place to follow the efforts to verify the proof", and added: "I
imagine the digestion process will take some time, though in this case at least we have a human
author to communicate with to assist with this task" [Community · C1]. The first AFP dispatch
appeared at 17:25:53 [Community · S4]. Moderators kept the Zulip thread on Lean topics and said they
had deleted off-topic messages [Community · V2 #642283561, #642305635]; Tao later added an update to his
post saying so; the post was last modified at 19:13:39 [Community · C1].

Simon DeDeo wrote at 17:49 that he was compiling on a local machine and
at 18:41 that the "Code compiles on our local machine" [Community · V2 #642292728, #642306246].
Sutherland's replay of every compiled module through the Lean kernel (`leanchecker`) finished at
about 18:17 with no rejections [Community · V1]. At 18:44 Buzzard summarised what was missing:
several people had reported that the code compiles, but "we still await a successful `comparator`
run", which would check that nothing redefines the symbols of the statement and, in paranoid mode,
that several independent kernels accept the proof [Community · V2 #642306912].

nanoda, a kernel written in Rust, was the first independent kernel to answer: it checked the full
61.57 GB export and exited 0 at 19:05:45, after 27 min 42 s on 80 threads
[Community · V1]; Sutherland posted the verdict at 19:09 [Community · V2 #642313194]. Separately,
GitHub user Infatoshi finished a third full compile at 19:05:21 and later published a nanoda receipt
for the closure of the five theorems, "Checked 1484729 declarations with no errors" [Community · V7].

At 19:16:22 Naskręcki posted that there was "a full confirmation from Andrew Sutherland who first
managed to finish the nanoda kernel run and comparator in paranoid mode" [Community · E8]. The
second half was not so: both versions of Sutherland's page that we read, those of 19:45 and 22:05,
list the paranoid kernels and `lake comparator` as still running [Checked · E8, V1: the archived
19:45 version and the live 22:05 version].

## 2.4 Masullo's draft (18:13–19:45)

The PDF of Masullo's draft records its creation at 18:13:46 [Checked · A4: PDF metadata]. At 18:18:42
Ravi Vakil, writing from a meeting of the American Mathematical Society, posted it on his blog under
the title "Hurried Announcement: Alessandro Masullo GRH" [Community · A5]. The original post says
that Conrad "has been looking closely at it for months and gave extensive feedback which is being
incorporated, and it is so far looking good", that "It is all human, with no AI", and asks people to
"quickly check it, formalize, fill any small gaps if they occur" [Community · A5, original text in
the capture of 18:35:24]. The Internet Archive captured the PDF at 18:35:24, and the archived bytes
equal our copy, so the draft has not changed since [Checked · A4, V12].

The draft claims GRH for all unitary Hecke characters of all number fields [Author · A4, p. 6]. Its
acknowledgements say that Masullo and Conrad "are aware of several glitches here and there", that
"In light of the current climate I am being advised to release the current version as it is", and
that "The math is complete, and only filling in some writing remains on several parts across this
long paper" [Author · A4, p. 6]. They end: "we are still here. We are very much alive. We are not going
anywhere." [Author · A4, p. 6]. The draft is unfinished in visible ways: footnotes such as "Insert
statement." remain, and Chapter 13, where GRH is to be deduced from the trace formula of Theorem
12.5.1.1, is two pages without a statement of its main theorem [Checked · A4, pp. 521–522; Part I,
§3; Chapter 0, §0.2].

AFP's expanded dispatch at 18:34 reported Vakil's announcement alongside Alpöge's [Community · P7].
The first public error report we found came at 18:56:45 from the X account @AcerFur: "ok GPT quickly
finds some errors, but idk how irreparable it is" [Community · E7]. At 19:16 David Loeffler opened a
separate Zulip thread, writing that "word is" Masullo had been working on this already and rushed
the announcement in response to Alpöge's [Community · V3 #642314625]; at 19:16:58 he opened a
Prove2Me mission to formalize the draft [Community · V3 #642314769; V14]. At 19:32 Tim Gehrunger
reported that an LLM judged the Main Theorem 12.5.1.1 incorrect, with "a pretty straight forward
counterexample", and at 19:42 that correcting one error reduces the theorem to a classical formula,
"at least that is what Astra and Fable seem to agree on" [Community · V3 #642318488, #642321263].

## 2.5 Independent kernels and the end of the "hot phase" (19:45–01:10)

At 19:45 Sutherland's page showed compile, axioms, `leanchecker` and nanoda passed, and recorded
that con-leche and con-ron "declined" with exit code 2, "not a rejection": those binaries did not
support one reflexive inductive type in the proof [Community · V1, version of 19:45]. At 19:53 he
posted the link to the page and to the export [Community · V2 #642323662]. Mario Carneiro asked why
lean4lean was failing and offered fixes; the bundled version could not read a Lean v4.33 core
library [Community · V2 #642324324, #642325559; V1]. DeDeo published his compiled `.olean` files at
20:13 so that others could run kernels without recompiling [Community · V2 #642328441; V8]. At
20:14 an issue on the Comparator repository reported a static audit of the import cone and of the
archive's few metaprogramming sites; the repository's notes were corrected at 20:43 [Community ·
E11, V5].

Szymon Teżewski reported at
20:40 that "con-leche ACCEPTS, took 3 minutes and 24s on 64 cores" [Community · V2 #642334721], and
posted its output at 20:52, all five theorems "justified by the solution" [Community · V2
#642338051]. Joachim Breitner explained at 20:54 that Sutherland's page had used an older con-leche
[Community · V2 #642338492]. Teżewski reported the pestka checker accepting at 20:58, and at 21:02
two checkers that did not get through, adding "neither is a rejection" [Community · V2 #642339366,
#642340706]. At 21:10 Breitner wrote: "I think the hot phase is over already?", and that "the
independent checking has been done and it passed without a hitch" [Community · V2 #642342529].
*Scientific American* published at 21:00 a report quoting Sutherland, "Honestly the chance that
anything is fishy here is approximately zero" [Community · P5].

In Sutherland's own runs, con-leche master accepted 1,468,418 declarations at 21:19:04,
its `--compare` mode confirmed all five theorems against the challenge at 21:19:12, and lean4lean,
run on the compiled files module by module, passed all 175,187 at about 21:55 [Community · V1,
version of 22:05]. He updated his page at 22:05 and announced it at 23:01 [Community · V1; V2
#642366000]. At 22:06 Teżewski posted a table of all the accepted runs [Community · V2 #642355040;
V9].

A second sandboxed compile completed on the LUMI supercomputer at 22:21: all 175,187 modules, with
`Main.olean` and `Statements.olean` hashes identical to Sutherland's [Community · V6]. Because
Sutherland's build ran without a sandbox, this match is the public evidence that his build was not
tampered with [Community · V1, caveats; V6].

To a question from Harald Helfgott, Sutherland answered at 23:25: "At this point I don't see
any realistic scenario in which this proof does not imply the statement of RH in mathlib", and at
23:41 that his `lake comparator --paranoid` run "should finish over the weekend, hopefully by
tomorrow night" [Community · V2 #642369995, #642372153]. *BBC News* published at 23:08:57
[Community · P15]. Bloomberg reported shortly after midnight that Sutherland had verified the code
on his own computer and had seen at least three other verifications on multiple systems
[Community · P22]. At 01:07 on 21 November Kim Morrison wrote: "Now that we've finished the 'let's
check the Lean proof carefully' stage, and there are essentially no remaining doubts as to whether
this is a correct proof", and set out the next stage: written accounts, Lean statements of
intermediate results, and clean-up into Mathlib and Tau Ceti [Community · G3]. At 01:56 Teżewski
reported that his own checker, Gruszka, accepts the whole export "in 4.5 min on my laptop"
[Community · V2 #642395135; V9].

## 2.6 The dispute over Masullo's draft (19:45–04:40)

At 20:05 Buzzard objected to using the Lean Zulip "as a place to
deconstruct someone's proof in public" when the author "did not ask for it to be disassembled in
this public way"; at 20:13 Floris van Doorn quoted Vakil's request that people check and formalize
the draft [Community · V3 #642326773, #642328387]. At 20:03:39 the README of the formalization
project `mccorvie/riemann-masullo` changed to "On hold", citing the Zulip report of a counterexample
to Theorem 12.5.1.1 [Community · V13]. *Scientific American* published at 20:40 the only words of
Conrad's we found: "To judge the success of the method requires the paper to reach a stage of more
final revision", and "It’s undergoing major revision" [Community · P4].

Refine Technologies posted an eight-page AI-assisted report at 21:12,
concluding that "in its present form, the manuscript does not establish the claimed results"; it
lists ten gaps or errors, among them the failure of a uniform bound on biorthogonal pairs at p. 451
[Community · E6]. The Prove2Me mission went live at 21:41 [Community · V3 #642349411; V14]. At 22:06 an issue on the
formalization project argued that Theorem 12.5.1.1 as printed fails for $\mathbb Q(i)$ and
$\mathbb Q(\sqrt{-3})$ and, once corrected, is Weil's explicit formula [Community · E4]. At 22:18
Loeffler reported a formal proof that RH follows from the draft's "Main Theorem" 12.5.1.1
[Community · V3 #642357563; V14]. Brent Yee linked the Refine report on Zulip at 22:38 [Community · V3
#642361492]. At 22:57:02 the formalization project returned to "Active", with a README that separates
the concerns about the main theorem, which "did not come from this formalization", from the small
errors it logs itself [Community · V13].

At 23:35 issue #1169 of the same project stated the p. 451 problem in detail: the draft needs a
constant bounding biorthogonal pairs uniformly in the zero, and nearby zeros of ζ on the critical
line make that impossible [Community · E2]. We reproduced the counterexample independently: an
elementary lower bound of about $1/d$ for two zeros at distance $d$, and a ball-arithmetic
computation that isolates two zeros 0.0377 apart and forces the product of norms above 20.4 for
$s=4$ [Checked · E9]. Others found it first: the Refine report stated it at 21:12 and #1169 at 23:35,
while our note dates from about 03:38 on 21 November [Checked · E2, E6, E9: timestamps]. At 01:56 on 21 November
Yan Ru Pei deposited on Zenodo a note proposing a repair of that step on the critical line only; it
says the arguments have not been checked by human experts [Community · E3]. By 04:39 the project's
errata list had 123 entries, which it says have not been reviewed by a specialist [Community · E1].

At 02:54:54 Vakil's post was edited [Community · A5: page metadata]. We compared the live page with
the archived original: the edit renames the author "Alessandro Maria Masullo", changes "so far
looking good" to "so far looking good to him", changes the plan to "have Brian work with
Alessandro for a year", and adds an "Update about 8 hours later" reporting problems found "with the
assistance of different AI models" and "(I make no claim as to the correctness of the proof
strategy.)" [Checked · A5: diff of the 18:35:24 capture against the live page].

Two points about Masullo remain unresolved [Open]. *Quanta* writes, without a source, that an earlier RH
proof he worked on "did not, in the end, hold up" [Community · P17; Open]. Several outlets call him a
postdoctoral researcher at Stanford, while his acknowledgements speak of returning to Stanford
[Community · P7, P12, P17, P21; Author · A4, p. 6; Open].

## 2.7 The next morning (01:10–05:57, 21 November)

A public build cache was merged into the Comparator repository at
04:27:42 [Community · V5]; an issue noted that `.olean` hashes depend on the build directory, and
pull requests to minimise imports remain open [Community · V5]. Kim Morrison posted instructions for
obtaining the repository with compiled files at 04:41 and a list of next steps at 04:52: minimise
imports, delete dead code, update Lean and Mathlib, and remove code duplicated in Mathlib
[Community · G3]. Readers' maps of the proof appeared as issues #3 and #5 of the Comparator
repository, alongside the LUMI reader's guide [Community · G1, G2]. Whether the archive may be modified and
redistributed is unsettled: it contains no licence file [Checked · A2; Part I, §1], and at 05:33
Thomas Murrills asked about keeping the original proof on one branch and iterating on another,
"assuming we can secure an Apache 2.0 license" [Community · V2 #642424791].

AP's story, carried by *The Independent* at 04:32, added a statement from Martin
Bridson, president of the Clay Mathematics Institute, calling it "an announcement of historic
significance" and warning that the way "to a place of real understanding will be long and
difficult" [Community · P9]. Earlier, *Nature* had quoted James Maynard, "If this fully checks out, it
is clearly a historic milestone in mathematics", and Andrew Granville, "What he released is garbled"
[Community · P18]. AFP had quoted Brian Conrey calling it "a monumental moment in human history",
while reporting that he had seen only the note and had asked for a manuscript [Community · P7]. BBC
News Japan published its translation at 03:52 [Community · P16].

BBC English and Japanese say that the Lean proof runs to more
than 250,000 pages, and New Scientist's explainer calls the 250,000-page text the proof and the Lean
code its translation; in the note those pages are the unposted informal text and Lean is the only
release [Checked · E13, against A1, p. 2, fn. 2]. BBC's headline misspells "Riemann", BBC Japanese
dates the message to Amodei to the 5th rather than the Sunday of 15 November, and TechCrunch calls
Vakil president of the "American Mathematics Association" [Checked · E13].

Our own checks that morning found nothing changed [Checked · A2, V1, V5]. At 04:52, 05:23 and 05:56 the archive parts
answered with the ETags recorded at download [Checked · A2]. Sutherland's page was byte-identical at
04:47, 05:24 and 05:56, still dated 22:05 [Checked · V1]. The Comparator repository had posted no
Comparator verdict by 05:56, and neither Zulip thread had a new verification report by 05:57
[Checked · V5, V2, V3]. Alpöge's home page was unchanged and no further write-up had appeared there
[Checked · A3], and no message in either Zulip thread comes from an account in his name [Checked ·
V2, V3: sender lists of our copies].

## 2.8 Where things stand (05:57 UTC, 21 November)

| Question | Claimed | Reported by others | Checked by us |
|---|---|---|---|
| Does the archive prove what it says? | RH and GRH, formalized "without assumptions" [Author · A1, p. 1] | — | The five statements are Mathlib's RH and GRH for Dirichlet L-functions only [Lean, read · Chapter 1] |
| Does it compile? | "its formalization is finished" [Author · A1, p. 1] | Three full compiles, one sandboxed, with matching `Main.olean` hashes between two of them [Community · V1, V6, V7]; further builds by DeDeo and others [Community · V8, V2] | Archive hash and the identity of the checked files with those posted on 20 November [Checked · A2, V12] |
| Do independent kernels accept it? | — | `leanchecker`, nanoda (twice), con-leche and its `--compare` mode, lean4lean, pestka, Gruszka [Community · V1, V7, V9] | — |
| What is still open in the machine check? | — | Lean default and paranoid kernels on the export, end-to-end `lake comparator`, sandboxed versus unsandboxed export [Open · V1, version of 22:05] | No newer result posted at 05:56 [Checked · V1, V5] |
| Is the proof understood? | A proper write-up is intended [Author · A1, p. 1] | Maps and AI-assisted guides; most of the arithmetic engine unread [Community · G1–G4] | Top layers read in Chapter 1 [Lean, read] |
| Is Masullo's draft a proof? | "The math is complete" [Author · A4, p. 6] | Gaps, errata and a disputed main theorem [Community · E1–E7]; Conrad: "undergoing major revision" [Community · P4] | The p. 451 bound fails [Checked · E9]; the status of Theorem 12.5.1.1 is [Open · E4] |

## 2.9 What we checked, and how

For readers who want to repeat our part of this chapter:

1. **Integrity of the posted files.** We joined the fourteen parts and hashed them; we compared the
   SHA-1 of our copies of the note, of parts 01 and 14 and of the Masullo PDF with the Internet
   Archive's digests of 20 November; and we repeated HEAD requests on all parts the next morning
   [Checked · A1, A2, A4, V12].
2. **Versions of the verification page.** We hashed the live page at three times and read its only
   archived version, of 19:45 [Checked · V1].
3. **The Zulip record.** We read both threads in full through Zulip's public API and cite messages by
   id; times are the server's [Checked · V2, V3].
4. **Edits and quotations.** We compared the archived and live texts of Vakil's post, and checked
   mechanically that every quotation in this chapter appears verbatim in our saved copies of the
   sources [Checked · A5, E13].
5. **Misreports.** We compared press statements and the post of 19:16 with the primary sources
   [Checked · E8, E13].
6. **The p. 451 bound.** We reproduced the counterexample with an elementary bound and a
   ball-arithmetic computation [Checked · E9].

We did not compile the archive or run any kernel: every result about compilation and kernels in this
chapter is [Community].

This chapter will be updated as the remaining checks finish. Until then, the current state is on
Sutherland's page (V1) and in the Comparator repository (V5).
