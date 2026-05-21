# Cover letter — submission to *Experimental Mathematics*

*Draft. Fill in the date and, optionally, suggested reviewers before
submitting through ScholarOne. The text below can be pasted into the
ScholarOne cover-letter field.*

---

[Date]

To the Editor-in-Chief
*Experimental Mathematics*

Dear Editor,

I am pleased to submit the manuscript **"Optimal strategies in the
all-heads coin game"** for consideration as a research article in
*Experimental Mathematics*.

**Summary of the contribution.**
The paper analyses a sequential coin-flipping game: a player starts
with *n* coins, each landing heads with probability *p*, and in each
round must set aside at least one coin showing heads, winning once all
coins have been set aside. The optimal winning probability *w(n,p)*
satisfies a Bellman equation with a nonlinear suffix-maximum operator.
We determine it completely at the fair coin *p = 1/2*; for *p > 1/2* we
identify the optimal strategy and obtain an explicit series for the
limit *W(p)*; and — the main contribution — for *p < 1/2* we carry out
a rigorous first-order perturbation expansion in *δ = 1/2 − p* that
explains the shape of the optimal-value sequence, in particular a
strict local minimum at *n = 5* and the absence of local maxima at
first order.

**Fit with the journal.**
The work is experimental mathematics in a concrete sense. The
perturbative results were found by exact, arbitrary-precision
computation of the Bellman recursion before they were proved; Section 5
reports the numerical experiments that motivate them and isolates a
remaining conjecture about the non-perturbative regime. In addition,
every numbered theorem, proposition, lemma, and corollary of the paper
has been formally verified in Lean 4 / Mathlib.

**On refereeing the formalization.**
The formalization is deliberately structured so that it can be assessed
by a referee who is *not* a Lean expert. The entire trust surface
consists of two short, human-readable files — `Challenge.lean` (the
theorem statements) and `Defs.lean` (the seven underlying definitions);
checking that these faithfully transcribe the manuscript requires only
mathematical reading, not Lean proficiency. The proofs themselves are
then checked mechanically by the Lean kernel, and the correspondence
can be reproduced with a single command via the Lean comparator.
Appendix A provides a line-by-line manuscript-to-Lean table with direct
hyperlinks, and the repository includes a reviewer's guide written for
non-Lean-experts. The formalization is therefore a verifiable
supplement and does not place an unusual burden on the review process.

**Code and data availability.**
The Lean formalization and the numerical code are openly available at
<https://github.com/pfaffelh/coins>. As the formalization is under
active development, I would suggest — in line with the journal's
supplementary-material policy — that it be referenced by link rather
than archived as a static supplementary file; I am happy to provide a
DOI-bearing archival snapshot if preferred.

**Disclosure on the use of AI tools.**
In the interest of full transparency, the manuscript states openly (in
the note on authorship in Section 1 and the development history in
Appendix A) that the drafting of prose, the Lean proof tactics, and the
numerical scripts were produced with Anthropic's Claude under my
direction. The mathematical ideas, the choice of research question, and
the decision to formally verify the results are my own, and I have
reviewed every line; I take responsibility for the manuscript. No
generative-AI system is listed as an author.

The manuscript is original, has not been published before, and is not
under consideration for publication elsewhere. There are no competing
interests to declare.

Thank you for considering this submission. I look forward to the
referees' comments.

Sincerely,

Peter Pfaffelhuber
Albert-Ludwigs-Universität Freiburg, Freiburg, Germany
Email: p.p@stochastik.uni-freiburg.de
ORCID: 0000-0002-6421-5460
