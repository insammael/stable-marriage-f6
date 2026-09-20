# Exposition Revision Report

Date: 2026-09-21  
Scope: final exposition-only revision of the v08 manuscript and supplementary material

## Files revised

- `public_repo/paper/f6_core_v08.tex`
- `public_repo/paper/SUPPLEMENTARY_MATERIAL_V08.tex`
- `public_repo/paper/MANUSCRIPT.pdf` (rebuilt)
- `public_repo/paper/SUPPLEMENTARY_MATERIAL.pdf` (rebuilt)

No Lean source, theorem certificate, verification artifact, GitHub state, or Zenodo state was changed.

## Edits made

### Manuscript

- Clarified the abstract equality sentence so that it says every one of the 36 man--woman pairs occurs in some stable matching, and removed the abstract's final Lean-artifact sentence.
- Recast the introduction positively around the classical rotation-poset framework and the new convex-block input.
- Moved the Biola/Roman Parks note to a restrained footnote attached to the introductory order-six result; retained the URL and access date.
- Removed the defensive sentence distinguishing an arbitrary list of matched pairs from a rotation.
- Added the requested triangle-edges explanation in Lemma 2.2.
- Compressed Remark 2.3 while retaining the restricted-instance/downset interpretation, the displayed inequality, and the reason for keeping the token proof.
- Left Remark 2.4 unchanged.
- Compressed Remark 3.5 to the forbidden induced graph patterns and the antichain/clique interpretation.
- Shortened the introduction to the no-re-entry argument without changing its proof.
- Left Lemma 4.2 and Remark 4.4 unchanged.
- Reorganized the proof of Lemma 4.5 into Claim 1 (transition pairs) and Claim 2 (outside neighbors), removed “Analogously,” and removed the unused stronger one-sided sentence.
- Rephrased the last equality consequence in Corollary 5.2 and removed the defensive necessary-condition disclaimer.
- Removed the uniqueness/classification disclaimer from Remark 5.3.
- Left the verification note and the journal-style AI declaration unchanged in substance.

### Supplementary material

- Added the author name `Myunglae Jo`.
- Tightened S3, S5, S6, S7, S8, S8.1, and S9 as requested, removing repeated defensive scope disclaimers while retaining the formalization boundary and the role of the auxiliary checks.

## Edits deliberately not made

- No theorem, lemma, proposition, corollary, or definition statement was changed.
- No displayed mathematical statement, constant, hypothesis, conclusion, citation fact, bibliography entry, or load-bearing proof step was changed.
- No change was made to Remark 2.4, Lemma 4.2, or Remark 4.4.
- No model names, vendors, prompts, or detailed AI workflow were added to the paper.
- No Lean, certificate, repository publication, GitHub push, or Zenodo operation was performed.

## Mathematical identity checks

The repository theorem-statement checker extracted 16 statements from both the pre-edit snapshot and the revised manuscript. Both normalized statement sets have SHA-256:

`f55a0f9b4411c3812c95348311637374aba4a8cfed8fb5ccd67edb9e58dba0f8`

Result: `THEOREM_STATEMENT_DIFF=PASS_IDENTICAL`.

All 53 displayed mathematical blocks occur in the same order with identical normalized content. Their common aggregate SHA-256 is:

`360c4fbe655975331af25a2e0fb902f37300d62c3b90e46d0f12a854d7b20d5e`

The eight bibliography keys are identical. Every pre-edit citation key remains present; the citation-key set is unchanged.

The AI declaration paragraph is byte-identical to the pre-edit paragraph apart from its unchanged source line wrapping.

## Lemma 4.5 proof-structure diff

The proof was only repartitioned:

1. The transition localization is now explicitly labeled Claim 1. Its two conclusions remain: an intersecting transition contributes zero new cross incomparable pairs, and a disjoint transition contributes at most three.
2. The outside-neighbor localization is now explicitly labeled Claim 2. Its conclusion remains `|Inc(x) ∩ U| ≤ 2`.
3. The concluding substitution in the pair count and the cases `t=7` and `t=6` are unchanged.

The nine displayed mathematical blocks in the statement and proof occur in the same order with identical normalized content. Their pre-edit and post-edit aggregate SHA-256 is:

`f0963e8529014004a8122e66ab9bbad1ac1dcdb6ba418b54761745c30574063c`

Thus equations (4.5)--(4.8), all intervening inequalities, `A_2+A_3≤30`, and the conclusion `|A(P)|≤46` are preserved exactly.

## Build and visual validation

- Manuscript: pdfLaTeX run twice; second-pass log contains 0 LaTeX errors and 0 unresolved references.
- Supplement: pdfLaTeX run twice; second-pass log contains 0 LaTeX errors and 0 unresolved references.
- Manuscript page count: 12 before, 11 after.
- Supplement page count: 4 before, 4 after.
- Visual audit: all 11 manuscript pages and all 4 supplement pages were rendered and inspected. No clipping, overlap, missing glyphs, malformed equations, or abnormal page breaks were found. The moved footnote, compressed remarks, Lemma 4.5 claims, author line, references, and final declarations render correctly.

## Final SHA-256 hashes

| Artifact | SHA-256 |
|---|---|
| `public_repo/paper/f6_core_v08.tex` | `b35d07bd798b6cd06301c255b8b1230906f4ad88dcb3ac65495c8071b7262afb` |
| `public_repo/paper/SUPPLEMENTARY_MATERIAL_V08.tex` | `54e490e8a24383ba63c3bff67e96518526f5d2dd00aa880007203c27c4f89f14` |
| `public_repo/paper/MANUSCRIPT.pdf` | `6be53ae4af95e2d788a9075c3401c4c8b3c6089373faa4d74c5491cbab261db7` |
| `public_repo/paper/SUPPLEMENTARY_MATERIAL.pdf` | `85b9553ad5387057e6a1cba25399c8f833e068e0babfecdaa33650582434a544` |

## Remaining release actions

The local exposition revision is complete. GitHub and Zenodo synchronization remain intentionally deferred; the rebuilt PDFs have not been pushed or uploaded.
