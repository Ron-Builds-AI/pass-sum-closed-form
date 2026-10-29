# Proof pieces for a Mellin-Barnes closed form of a pass sum

Ronald Lee Hampton Jr., VetTech Homefront LLC. 27 October 2026. Version 1.1, 29 October 2026 (version 1.0: 28 October 2026).

Collaborator: Elena Gortcheva, PhD, Program Director, Data Analytics.

## What this is

A pass sum taken from Kim and Thorne's 1991 paper on vacuum fluctuations and time machines (their equation 67), written in a closed form
through a Mellin-Barnes representation, with written proofs of the pieces the author's earlier proof draft left open:

- Lemma L: an exact representation of the sum's Mellin transform on the left half plane as an absolutely convergent double series;
- Theorem P3: a growth bound far to the left, at every real p;
- Theorem P1: the expansion for 0 < u < 1 at every p < 3, integer p included;
- Theorem P2: what converges for u >= 1;
- Proposition 4.4: where the residues at the meeting poles vanish at integer p: exactly on a chain of integers given by the Pell-type
  equation y^2 - 3b^2 = -2, with b = 5 - 2p (the same chain as Archimedes' approximations of the square root of 3).

## Status, at its real size

- Checked by an AI instrument (exact arithmetic and high-precision numerics; the scripts and their outputs are in `checks/`), read by no
  mathematician yet. A review by a mathematician is the next step.
- Version 1.1 carries the corrections from a further read by AI instruments (29 October 2026). A remark on weights that do not read the
  same both ways was wrong in 1.0 and is rewritten; several hypotheses and steps are now stated in full; the citations were checked at
  the source. It also writes out the one result of the author's earlier draft that the proofs use (Claim 3.1). It proves that at the
  weights (1,4,2) every vanishing pair lies on one chain, and it gives a vanishing pair at (1,9,2) that does not. It is still read by no
  mathematician.
- A search of the published sources reached (16 October 2026) did not find this closed form. Not found is not the same as new; a full
  search is still owed.
- No physics claims are made. The sum comes from a physics paper; what is offered here is mathematics about the sum.

## Files

- `paper/Hampton_pass-sum_proof-pieces_2026-10-27_r5d.pdf` and `.tex` (with its plot data in `paper/fig_r5/`): the proof pieces,
  version 1.1. The version 1.0 files, `..._r5b.pdf` and `.tex`, stay beside them.
- `paper/Hampton_problem-statement_for-outside-readers_2026-10-28.pdf`: the problem stated with every symbol and its range, where the
  logarithms vanish (the Pell chain), the standing, and references (five pages; written for version 1.0).
- `checks/`: the checking scripts (Python) and what they printed. `check_r5d_2026-10-29.py` is the checker of version 1.1 (22 checks).
  The earlier checkers look for the plot data in `fig_r5/` beside `checks/`; to run one, copy `paper/fig_r5/` there first.
- `CITATION.cff`: how to cite this work.
- `SHA256SUMS.txt`: a fingerprint of every file in this version, as committed (LF line ends). `SHA256SUMS.txt.ots`: an OpenTimestamps
  proof for that list (it carries only the list's hash; verifiable at opentimestamps.org), submitted on 29 October 2026; it is complete
  once the Bitcoin chain confirms it.
- `timestamps/SHA256SUMS_2026-10-28.txt` and its `.ots`: version 1.0's fingerprint list (28 October 2026) and its OpenTimestamps proof,
  confirmed in Bitcoin blocks 973597, 973607 and 973623.
- `timestamps/SHA256SUMS_2026-10-27.txt` and its `.ots`: the first version's fingerprint list (27 October 2026) and its OpenTimestamps
  proof, confirmed in Bitcoin blocks 973446 and 973453.

## License

The paper (`paper/`) is under CC BY 4.0 and the checking scripts (`checks/`) under the MIT License; see `LICENSE.md`. As CC BY 4.0
states, patent and trademark rights are not licensed under it.

Drafted with AI assistance and verified against my records. Reviewed and approved by Ron Hampton.
