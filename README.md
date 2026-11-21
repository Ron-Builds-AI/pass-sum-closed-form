# Proof pieces for a Mellin-Barnes closed form of a pass sum

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23780635.svg)](https://doi.org/10.5281/zenodo.23780635)

To cite this work, use the concept DOI 10.5281/zenodo.23780635 for all versions, and 10.5281/zenodo.23780636 for version 1.2.

Ronald Lee Hampton Jr., VetTech Homefront LLC. 27 October 2026. Version 1.5, 20 November 2026. Earlier versions: 1.4 (6 November 2026), 1.3 (30 October 2026), 1.2 (29 October 2026), 1.1 (29 October 2026), 1.0 (28 October 2026).

Collaborator: Elena Gortcheva, PhD, Program Director, Data Analytics.

## What this is

Here "closed form" means a Mellin-Barnes integral representation from which the expansions follow by residues; it is not an
expression in elementary functions.

A pass sum taken from Kim and Thorne's 1991 paper on vacuum fluctuations and time machines (their equation 67), written in a closed form
through a Mellin-Barnes representation, with written proofs of the pieces the author's earlier proof draft left open:

- Lemma L: an exact representation of the sum's Mellin transform on the left half plane as an absolutely convergent double series;
- Theorem P3: a growth bound far to the left, at every real p;
- Theorem P1: the expansion for 0 < u < 1 at every p < 3, integer p included;
- Theorem P2: what converges for u >= 1;
- Proposition 4.4: where the residues at the meeting poles vanish at integer p: exactly on a chain of integers given by the Pell-type
  equation y^2 - 3b^2 = -2, with b = 5 - 2p (Archimedes' lower bound for the square root of 3, 265/153, is a point of this chain; his upper bound, 1351/780, lies on the companion equation x^2 - 3z^2 = 1).

Version 1.5 adds, in `lean/`, a Lean 4 proof of the paper's integer part: the Pell chain, Proposition 4.4, Proposition W, and the
identities of Proposition B. The section "The Lean proof" below says what it proves and what it takes as given.

## Status, at its real size

- Checked by an AI instrument (exact arithmetic and high-precision numerics; the scripts and their outputs are in `checks/`), read by no
  mathematician yet. A review by a mathematician is the next step.
- Version 1.1 carries the corrections from a further read by AI instruments (29 October 2026). A remark on weights that do not read the
  same both ways was wrong in 1.0 and is rewritten; several hypotheses and steps are now stated in full; the citations were checked at
  the source. It also writes out the one result of the author's earlier draft that the proofs use (Claim 3.1). It proves that at the
  weights (1,4,2) every vanishing pair lies on one chain, and it gives a vanishing pair at (1,9,2) that does not. It is still read by no
  mathematician.
- Version 1.2 (29 October 2026) changes no statement, proof, number or formula of 1.1. It adds disclosures to the paper's list of
  what is open (Section 7): no AI verification pass opened Kim and Thorne's paper, so the identification of this sum with their
  equation 67 rests on the author's reading; the proceedings details of Ueno and Nishizawa's paper were not verified; the second
  chain at (1,9,2), three smaller fixes and the paper's sentence on how it was made were written after the last AI verification
  pass and have had no later independent read; and the version 1.0 paper carries the earlier remark.
- Version 1.3 changes no theorem, proof or formula of 1.2. An independent read of every mention of Archimedes in the paper (29 October
  2026; exact integer checks, Davies' paper read at the source, Heath's 1897 edition read in its archive.org text) found no mention
  wrong and three sentences to reword. Revision r5f rewords them: the Status paragraph now says that Archimedes' bound lies on the chain, not that it belongs to the
  record of Pell's equation; Section 4.7 names all four vanishing pairs that carry 153, where it named two (the other two are their
  images under the swap of Section 4.6); and the entry for Heath's edition calls the square brackets Heath's insertions. The new
  wordings have had no later independent read.
- Version 1.4 (6 November 2026) changes no statement, formula or number of 1.3. Revision r5g opens with one sentence on what
  "closed form" means here. It writes out steps that a read of r5f by an AI system of another maker (Meta AI, 2 November 2026) asked
  to see: the uniform Stirling constant on the horizontal sides of Lemma L's contour, and the poles that a zero of 1/Gamma cancels
  there; the lattice sum and the constants of Theorem P3, and why its cancellation is exact; the finite part's dependence on the tail
  bound of Claim 3.1, and the sign of the logarithm against the author's earlier draft; and the expansions, degree bounds and
  descents of the Pell part. It cites the related work that a search of the open record (2 November 2026) found, with page and
  equation. A new checker, `checks/check_r5g_2026-11-06.py`, checks the added steps, and the checker of 1.1 was run again unchanged.
  The additions have had no independent read.
- Version 1.5 (20 November 2026) changes no statement, proof, number or formula of 1.4; the paper is still r5g. It adds `lean/`, a
  Lean 4 proof, with the Mathlib library, of the integer and binomial part of Sections 4.5 and 4.6, described in the next section. The
  Lean file was drafted with an AI instrument at the author's direction (2 November 2026), and Lean's kernel checks it. No mathematician
  has read it yet.
- Searches of the published sources reached (16 October and 2 November 2026, the second with a citation check at the source) did not
  find this closed form, or Kim and Thorne's sum treated by a Mellin transform. The second found Lemma L's unshifted case in print
  three times (Ueno and Nishizawa) and the integer pairs of the Pell chain in print (Luca and Szalay, 2004; the OEIS), with no tie to
  logarithmic residues; revision r5g cites them. MathSciNet and zbMATH were not searched. Not found is not the same as new.
- No physics claims are made. The sum comes from a physics paper; what is offered here is mathematics about the sum.

## The Lean proof

`lean/PellPilot/PassSumPell.lean` (1,814 lines, 128 theorems) proves, in Lean 4 with Mathlib, the integer and binomial part of Sections
4.5 and 4.6 of the paper. It is the file compiled on 2 November 2026, unchanged. Its header cites revision r5f, whose statements
r5g keeps (version 1.4 changed none), at the same section numbers: Proposition 4.4 in Section 4.5, Proposition W in Section 4.6. One
slip in the header: the notation it cites as Section 2.2 is Section 1.2, in r5f and in r5g.

What it proves:

- The chain of y^2 - 3b^2 = -2. The pairs (y_k, b_k) start at (1, 1) and step by (y, b) -> (2y + 3b, y + 2b), so that
  y_k + b_k sqrt(3) = (1 + sqrt(3))(2 + sqrt(3))^k. Every pair solves the equation, and every solution with y >= 0 and b >= 0 is one of
  them (`chain_complete`). The proof is a descent: (y, b) -> (2y - 3b, 2b - y) keeps the equation and, while b >= 2, lowers b and leaves
  both entries positive, and the only solution with y >= 0 and 0 <= b <= 1 is (1, 1) (`down_pos_lt`, `base_of_le_one`,
  `descent_reaches_base`). Also the recurrences, the parity, and the first eight pairs.
- The reduction of the vanishing condition to that chain, proved for all integers in range, not checked on a grid of values. With the
  paper's binomial and Q_n(s), at the weights (1, k, 1): Q_{p+l}(-l) = (-1)^n B_{-p}(l) with n = p + l (`Q_w1k1`); Step 3 of the proof
  of Proposition 4.4 as an identity in the integers (`step3_identity`); and, at p <= 1 and l >= -p, B_{-p}(l) = 0 exactly when
  t^2 - ktx + x^2 = t + x, with t = 2 - p and x = l + p (`Bk_eq_zero_iff_Ek`).
- Proposition 4.4 (a) to (d) as the paper states it, at the weights (1, 4, 1) (`prop44_a`, `prop44_b`, `prop44_c`, `prop44_c_set`,
  `prop44_d_p`, `prop44_d_l`), with the values and recurrences of p_k and lambda_k that it lists, and the examples after it
  (`prop44_examples`). In one statement (`vanishing_pairs`): for p <= 2 and l >= max(0, -p), Q_{p+l}(-l) = 0 exactly when (p, l) is
  (p_k, lambda_{k-1}) or (p_k, lambda_k) for some k >= 1.
- Proposition W (a) to (e) at the weights (1, k, 1), for every integer k, with the descent of W (d) (`propW_d`, `propW_d_descent`); the
  bridge at k = 4 to the chain above; the identities of Proposition B; and the forms at k = 2 and k = 3.

What it takes as given: the analytic link. That the coefficient G_l of the logarithmic term equals R_l Q_{p+l}(-l)/L (the display before
Proposition 4.4, from Lemma 4.2 (c)) is not proved in Lean. The file proves the algebraic half: given that formula, with
R_l = (-1)^l binom(l+2, 2) and L not 0, G_l = 0 exactly when Q_{p+l}(-l) = 0 (`G_eq_zero_iff`). Not in Lean at all: Lemma L, Theorems
P1, P2 and P3, the remark of one curve through every vanishing pair, and weights that are not symmetric, such as (1, 4, 2) and
(1, 9, 2). The statements about Q_n hold over any field of characteristic zero, which covers the paper's complex numbers.

Lean checks that each proof follows from the definitions. It does not check that the definitions and the statements say what the paper
means: they (the `def` lines and the theorem statements) are the part to hold against the paper.

Build. The versions are pinned: Lean 4.36.0-rc2 in `lean/lean-toolchain`, and Mathlib at revision v4.36.0-rc2 (commit 9d581dfff2e4)
in `lean/lakefile.toml` and `lean/lake-manifest.json`. With elan (Lean's toolchain installer) on the path, in `lean/`:

```
lake exe cache get
lake env lean PellPilot/PassSumPell.lean
```

The first line fetches Mathlib and its prebuilt files (about 7 GB on disk, an estimate that was not measured). It has not been run from
this folder or from a clean checkout. The second line, `lake env lean`, is the build line and the recorded route; it prints one line
per theorem. `lake build` is not the route and was not run: the lakefile names a library, `PellPilot`, whose root file `PellPilot.lean`
is not in this folder. On 20 November 2026 the build line was run on this file on the author's machine, with the Mathlib fetched
on 2 November 2026: exit code 0, no errors and no warnings, and 128 lines out, byte for byte the recorded output of 2 November 2026.
They are kept as `lean/build_output_2026-11-20.txt`. Outside its comments, the file holds no `sorry`, no `axiom` declaration, no
`native_decide` and no `set_option`.

Axioms. The file ends with a `#print axioms` line for each of its 128 theorems. In the printout, 125 theorems depend only on Lean's
three standard axioms, `propext`, `Classical.choice` and `Quot.sound`, or on some of them, three depend on none, and `sorryAx` (the
mark of an unproved step) does not appear. The lines for the theorems named above:

```
'PellPilot.chain_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.down_pos_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.base_of_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.descent_reaches_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.Q_w1k1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.step3_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.Bk_eq_zero_iff_Ek' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.prop44_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.prop44_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.prop44_c' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.prop44_c_set' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.prop44_d_p' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.prop44_d_l' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.prop44_examples' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.vanishing_pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.propW_d' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.propW_d_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPilot.G_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Files

- `paper/Hampton_pass-sum_proof-pieces_2026-10-27_r5g.pdf` and `.tex` (with its plot data in `paper/fig_r5/`): the proof pieces,
  versions 1.4 and 1.5. The version 1.3 files, `..._r5f.pdf` and `.tex`, the version 1.2 files, `..._r5e.pdf` and `.tex`, the version 1.1
  files, `..._r5d.pdf` and `.tex`, and the version 1.0 files, `..._r5b.pdf` and `.tex`, stay beside them.
  Where the paper cites the author's working records by file name (in typewriter type), those records are not in this repository.
- `paper/Hampton_problem-statement_for-outside-readers_2026-10-28_r2.pdf`: the problem stated with every symbol and its range, where
  the logarithms vanish (the Pell chain), the standing, and references (five pages; revised for version 1.1). The version 1.0 page,
  without `_r2`, stays beside it.
- `checks/`: the checking scripts (Python) and what they printed. `check_r5d_2026-10-29.py` is the checker of versions 1.1 to 1.5
  (22 checks; 1.2 to 1.5 change nothing it checks), and `check_r5g_2026-11-06.py` checks the steps that version 1.4 writes
  out (11 checks; it needs sympy and mpmath). The earlier checkers look for the plot data in `fig_r5/` beside `checks/`; to run one,
  copy `paper/fig_r5/` there first.
- `lean/`: the Lean proof and what builds it (see "The Lean proof" above). `PellPilot/PassSumPell.lean` is the proof;
  `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` pin Lean and Mathlib; `build_output_2026-11-20.txt` is the build line's
  whole output; `.gitignore` keeps a local build's `.lake` folder out of git; `LICENSE` is the MIT License.
- `CITATION.cff`: how to cite this work.
- `.zenodo.json`: what Zenodo reads when it archives a release (title, author, abstract with a line on how the work was made, keywords,
  version). It names one license for the Zenodo record, CC BY 4.0; `LICENSE.md` gives the licenses of `paper/`, `checks/` and `lean/`.
- `SHA256SUMS.txt`: a fingerprint of every file in this version; text files carry LF line ends in every clone, so the list matches
  any checkout or download. `SHA256SUMS.txt.ots`: an OpenTimestamps proof for that list (it carries only the list's hash; verifiable
  at opentimestamps.org), made when this version is released; it is complete once the Bitcoin chain confirms it.
  Version 1.4's list is confirmed in Bitcoin block 974994; its proof (it carries only the list's hash; verifiable at opentimestamps.org)
  is kept in `timestamps/`, listed below.
- `timestamps/SHA256SUMS_v1.4_2026-11-06.txt` and its `.ots`: version 1.4's fingerprint list (6 November 2026) and its OpenTimestamps
  proof, confirmed in Bitcoin blocks 974994, 975023 and 975026.
- `timestamps/SHA256SUMS_v1.3_2026-10-30.txt` and its `.ots`: version 1.3's fingerprint list (30 October 2026) and its OpenTimestamps
  proof, confirmed in Bitcoin blocks 973805, 973821 and 973824.
- `timestamps/SHA256SUMS_v1.2_2026-10-29.txt` and its `.ots`: version 1.2's fingerprint list (29 October 2026) and its OpenTimestamps
  proof, confirmed in Bitcoin block 973733.
- `timestamps/SHA256SUMS_2026-10-29.txt` and its `.ots`: version 1.1's fingerprint list (29 October 2026) and its OpenTimestamps proof,
  confirmed in Bitcoin blocks 973691 and 973699.
- `timestamps/SHA256SUMS_2026-10-28.txt` and its `.ots`: version 1.0's fingerprint list (28 October 2026) and its OpenTimestamps proof,
  confirmed in Bitcoin blocks 973597, 973607 and 973623.
- `timestamps/SHA256SUMS_2026-10-27.txt` and its `.ots`: the first version's fingerprint list (27 October 2026) and its OpenTimestamps
  proof, confirmed in Bitcoin blocks 973446 and 973453.

## License

The paper (`paper/`) is under CC BY 4.0, and the checking scripts (`checks/`) and the Lean proof (`lean/`) are under the MIT License; see
`LICENSE.md`. As CC BY 4.0
states, patent and trademark rights are not licensed under it.

Drafted with AI assistance and verified against my records. Reviewed and approved by Ron Hampton.
