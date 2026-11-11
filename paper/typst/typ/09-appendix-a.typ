// The harness pulls this file in with #include, which does not pass on the template's definitions; rtable needs this import.
#import "/template.typ": rtable

#counter(heading).update(0)
#set heading(numbering: (..n) => [Appendix #numbering("A", ..n).], supplement: [Appendix])

#page(flipped: true, margin: (x: 0.7in, y: 0.8in))[
= The eleven runs <sec-appendix-a-the-eleven-runs>

Times are UTC, from the files `logs/<label>.start` and `logs/<label>.end` of each bundle; every exit code is 0.
"Thm" is the number of theorem names in the Comparator configuration, "Def" the number of definitions in the challenge.
The last two columns give the first eight hexadecimal digits of the sha256 of the add-on tarball (for run 1, of the kit) and of the receipt tarball; `CHECKSUMS.sha256` has them in full.

#rtable(
  columns: (auto, auto, 1fr, auto, 62pt, auto, 84pt, auto, auto, auto),
  align: (center, left, left, right, left, left, left, left, left, left),
  size: 8.4pt,
  header: ([Run], [Label], [What was judged], [Thm], [Def], [Kernels], [Date, start to end (UTC)], [Verdict], [Add-on], [Receipt]),
  [1], [`qrh-main`], [OpenAI's `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`, openai/math at `adc7f124`], [1], [no count given], [Lean], [2026-10-27, 17:43:45 to 19:38:23], [PASS], [`e0745073`], [`d8670539`],
  [2], [`zeta23-main`], [Anthropic's zeta23, 17 statements, anthropics/formal-math at `16a5ce41`], [17], [not counted; no holes], [Lean, NanoDa], [2026-10-28, 11:08:56 to 11:29:58], [PASS], [`958abb9f`], [`e0b9a4d9`],
  [3], [`mnf-library`], [`MNF.RH` v1 on a copy of run 1’s tree], [40], [17, as holes], [Lean], [2026-10-28, 00:20:02 to 00:32:46], [ACCEPTED], [`295ee9c6`], [`f9180842`],
  [4], [`mnf-library-v2`], [`MNF.RH` v2 on a copy of run 1’s tree], [43], [17], [Lean], [2026-10-28, 03:25:44 to 03:39:13], [ACCEPTED], [`933c5ba8`], [`c6142a40`],
  [5], [`mnf-library-v3`], [`MNF.RH` v3, with the Sturm–Liouville file, on a copy of run 1’s tree], [87], [41], [Lean], [2026-10-29, 05:56:47 to 06:10:47], [ACCEPTED], [`3668e138`], [`023d7ada`],
  [6], [`zeta23-mnf`], [`MNF.RH` and the restatement of zeta23’s Theorems A to D, in run 2’s checkout], [62], [23], [Lean, NanoDa], [2026-10-29, 02:06:38 to 02:12:34], [ACCEPTED], [`958abb9f`], [`1476f568`],
  [7], [`zeta23-density`], [the layer, add-on v2: counting vocabulary, restatements of zeta23, the author's operator bookkeeping, first lemmas toward Bohr–Landau], [124], [66], [Lean, NanoDa], [2026-11-03, 21:05:57 to 21:13:50], [ACCEPTED], [`5dc41dff`], [`975b2178`],
  [8], [`zeta23-density-v3`], [add-on v3: adds Bohr–Landau for $delta > 1 slash 6$], [270], [76], [Lean, NanoDa], [2026-11-03, 22:03:08 to 22:09:37], [ACCEPTED], [`c0958d53`], [`0588555d`],
  [9], [`zeta23-density-v4`], [add-on v4: adds Bohr–Landau for every $delta > 0$], [334], [81], [Lean, NanoDa], [2026-11-04, 00:52:20 to 00:58:43], [ACCEPTED], [`fb74e8a2`], [`0d1919e4`],
  [10], [`zeta23-density-v5`], [add-on v5: adds the displacement sum and the zero-density estimate], [480], [98], [Lean, NanoDa], [2026-11-04, 14:38:23 to 14:45:29], [ACCEPTED], [`2d2cf058`], [`37a806b2`],
  [11], [`zeta23-density-v6`], [add-on v6: adds the pair-measure module and the absence of real zeros in $(0,1)$], [534], [110], [Lean, NanoDa], [2026-11-11, 00:02:37 to 00:17:52], [ACCEPTED], [`99575a1e`], [`ca07a500`],
)

Runs 1 and 2 are cold.
Runs 6 to 11 are recorded as warm, cold only for the modules each add-on introduces; the bundles of runs 3 to 5 record no run type.
The numbering is the record's: by start time the order is 1, 3, 4, 2, 6, 5, 7, 8, 9, 10, 11.
Runs 2 and 4 to 11 list no definition hole, so every definition that a claimed statement refers to is compared by name, type and body; "Def" counts the `def` declarations in the challenge sources and is an upper bound for the bodies compared (in run 11, for instance, `Zeta23.BL.CG`, `Zeta23.BL.meanSquareB` and `Zeta23.BL.A₀` are counted and no claimed statement refers to them); the receipts of runs 1 and 2 give no count.
Each of runs 8 to 11 re-judges the layer of the previous run together with the new modules.
Runs 2 and 6 share one deposited add-on tarball; run 2’s receipt records another manifest hash, so a different version, by the evidence given in~@sec-receipts-and-the-verifier an earlier one, launched run 2.
The verifier does not compare the sources hashed in run 6 with that tarball; compared by hand for this paper, the five Lean sources are byte-identical.
]
