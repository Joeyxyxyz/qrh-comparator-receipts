// Line-break opportunities inside a long code name (the helper of typ/10-appendix-b.typ): after each occurrence of
// the given character the name may break. The empty box has no size and no text: nothing is inserted into the
// name, and a copied name stays intact.
#let breakable(it, after) = {
  let parts = it.text.split(after)
  for (i, p) in parts.enumerate() {
    if i + 1 < parts.len() { raw(p + after); box() } else { raw(p) }
  }
}

= Authorship and use of AI tools <sec-authorship-and-use-of-ai-tools>

The author, Joey Messina, conceived the MNF framework, set the goals, operated every run and is responsible for every claim.

One qualification of "operated": the kit and every add-on ship an instruction file written for a Claude Code session that, as the unprivileged user, starts the scripts, waits, runs the report script and reports the result.
The README files of the kit and of the first three add-ons describe the run through such a session; those of the six later add-ons give the commands to type and offer the session as an alternative.
The record attributes the operation of every run to the author.
For runs 7 to 11 the working log says how each was started: for runs 7 to 10 a Claude Code session working with the author typed one command line into a terminal (copy the add-on to the unprivileged account, open a shell as that account, run the three scripts), and the author authorized it by entering his password; run 11 he started himself from a terminal window with the same command line.
For runs 1 to 6 the record does not say whether the commands were typed by him or issued by such a session at his request.

The kit and add-on scripts, the documents of the record, the Lean files of runs 7 to 11 except four supporting files supplied by the author, and the text of this paper were produced with Claude Code~@claude-code, Anthropic's coding agent, under the author's direction.
According to `NOTICE`, the larger files of runs 8 to 11 were written by parallel agents from written plans, merged, and corrected after adversarial reviews of the prose; the idea behind `Cube.lean` is recorded as the author's.
`NOTICE` and the working log name no human reviewer: the log calls one of these reviewers a "workflow agent", and `NOTICE` speaks of "independent model reviewers" for the earlier files.
The text of this paper was likewise reviewed by model reviewers before the deposit.
The files of the record name no model version.
The commit messages of the repository do: the four commits up to run 10 carry the trailer "Co-Authored-By: Claude Fable 5.1", and the commit of run 11 and the commits made while this paper was prepared "Co-Authored-By: Claude Fable 5.2".
A trailer is attached to a commit, not to a file, and the record does not say which model wrote which Lean file.

`NOTICE` adds three qualifications.
It attributes six files of `MNF.RH` (`Core`, `Gap`, `Hypotheses`, `Unconditional`, `Reduction` and `Schrodinger`) to the author's earlier corpus, consolidated on 2026-10-27/28, and says that the additions of 2026-10-28/29 were written with Claude Code: the files `Counting`, `Zeta23Restated` and `GapDensity`; the three gap theorems added in run 4 (#breakable(`spectralGapHyp_iff_zeroFree_strip`, "_"), #breakable(`spectralGapHyp_three_eighths_iff_of`, "_") and #breakable(`spectralGapHyp_three_eighths_iff`, "_"), which sit in `Hypotheses` and `Unconditional`); the proposition forms of `GapMechanism` and `SchrodingerRealization`; and the port of the Sturm–Liouville file.
Four supporting files of the layer (`Zeta23/Superlinear.lean`, `OffLine.lean`, `BohrLandau.lean`, `MNFBridge.lean`) were supplied by the author.
For the rest of the six corpus files, their consolidation of 2026-10-27/28 included, and for these four supporting files, the record does not say which tool, if any, drafted them.
The Sturm–Liouville file of run 5 was co-authored by Aristotle (Harmonic); see~@sec-the-sturmliouville-file-and-its-co-authorship.
A problem file for Aristotle prepared on 2026-11-03 for the last step of the Bohr–Landau proof (notes, `aristotle/`) was, according to the plan document of run 9, superseded by the agents' proof of the same chain; it has no part in the layer.
The corpus itself is not part of the record and was not examined for this paper; the register's inventory counts 241 documents and assigns the files outside the RH line to "Zenodo Vol 1 (operator core) and Vol 3 (physical applications)".
That inventory lists "the aristotle stubs 1–3" and an "aristotle\_stress\_test\_synthesis" within the RH line and `_aristotle` variants outside it, and the header of the Sturm–Liouville file calls its three corpus variants "all Aristotle".
These names suggest that Aristotle's part in the corpus is not limited to that one file; the record does not say which statements of the six consolidated files, if any, descend from such outputs.

One of the two artifacts re-checked, zeta23, is Anthropic's, and according to its README its Lean code was written by Claude; the scripts that repeated its check, and this text, were produced with Claude Code, a product of the same company.
In run 2’s receipt "independent" can mean no more than another machine, another operator and another launcher.
The acceptance itself is the output of Comparator~@comparator, of Lean's kernel~@lean4 and of NanoDa~@nanoda, not of a language model.

The correctness of the Lean proofs does not rest on who or what wrote them: every claimed theorem of runs 3 to 11 was accepted by Comparator and the Lean kernel, and in runs 6 to 11 by NanoDa, against a statement printed in its bundle.
No tool checks that a Lean statement matches its English reading, or that the prose is right; where they differ, the Lean statements and the receipts govern.

#heading(numbering: none)[Acknowledgments] <sec-acknowledgments>

The theorem that $zeta$ has no zeros with real part above $7 slash 8$, and its Lean proof, are OpenAI's~#cite(<openai-math>).
The theorem that more than two thirds of the zeros are simple and on the critical line belongs to Alpöge and Furman~@alpoge-furman and to Anthropic, whose zeta23 formalizes it~@anthropic-formal-math; a script of that project informed the structure of the kit's verification scripts.
Comparator and lean4export are the Lean FRO's~@comparator #cite(<lean4export>).
Every file judged here builds on Mathlib~@mathlib, the work of its community.
Aristotle (Harmonic)~@aristotle co-authored the Sturm–Liouville file.
The Euler–Maclaurin representation used here comes from the PrimeNumberTheoremAnd project~@pnt-plus through zeta23; NanoDa~@nanoda and landrun~@landrun are the work of their authors.
Naming them implies no endorsement.
