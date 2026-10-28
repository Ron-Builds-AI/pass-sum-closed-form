# Proof pieces for a Mellin-Barnes closed form of a pass sum

Ronald Lee Hampton Jr., VetTech Homefront LLC. 27 October 2026. Version 1.0, 28 October 2026.

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
- A search of the published sources reached (16 October 2026) did not find this closed form. Not found is not the same as new; a full
  search is still owed.
- No physics claims are made. The sum comes from a physics paper; what is offered here is mathematics about the sum.

## Files

- `paper/Hampton_pass-sum_proof-pieces_2026-10-27_r5b.pdf` and `.tex` (with its plot data in `paper/fig_r5/`): the proof pieces.
- `paper/Hampton_problem-statement_for-outside-readers_2026-10-28.pdf`: the problem stated with every symbol and its range, where the
  logarithms vanish (the Pell chain), the standing, and references (five pages).
- `checks/`: the checking scripts (Python) and what they printed.
- `CITATION.cff`: how to cite this work.
- `SHA256SUMS.txt`: a fingerprint of every file in this version. `SHA256SUMS.txt.ots`: an OpenTimestamps proof for that list (it carries
  only the list's hash; verifiable at opentimestamps.org); it is pending until the Bitcoin chain confirms it, a few hours after it is made.
- `timestamps/SHA256SUMS_2026-10-27.txt` and its `.ots`: the first version's fingerprint list (27 October 2026) and its OpenTimestamps
  proof, confirmed in Bitcoin blocks 973446 and 973453.

## License

The paper (`paper/`) is under CC BY 4.0 and the checking scripts (`checks/`) under the MIT License; see `LICENSE.md`. As CC BY 4.0
states, patent and trademark rights are not licensed under it.

Drafted and fact-checked with an AI assistant from my own records, measurements and decisions. I read and edited every sentence and I am responsible for its contents.
