# Final Micro-Editorial Report

Date: 2026-09-21  
Scope: final micro-editorial pass before public synchronization

## Authorized edits completed

### Main manuscript

- Confirmed that `rem:restriction` had no references anywhere in the public repository, then deleted the entire former Remark 2.3 without replacement. The remaining Section 2 numbered environments close the resulting numbering gap automatically.
- Removed the undefined phrase “saturated rotation instances” from the introduction.
- Replaced “human proof” and “human mathematics” wording in the verification note with neutral formalization-scope language.
- Added one code-availability sentence linking to `https://github.com/insammael/stable-marriage-f6`.
- Removed only the redundant classification disclaimer from Remark 4.7.
- Added PDF Title and Author metadata through `\hypersetup`; the visible title and author are unchanged.

### Supplementary material

- Added PDF Title and Author metadata through `\hypersetup`; the visible title and author are unchanged.
- Replaced the remaining “human upper-bound” wording with neutral scope language.
- Defined `q` locally as the number of transitions in a run before its first use in S2.
- Added the public source and reproducibility repository URL once in S5.
- Renamed S6 to “Components outside the formalization” and replaced “human statements” wording with neutral formalization-scope language.

## Deliberately unchanged

- No theorem, lemma, proposition, corollary, or definition statement was altered.
- Lemma 4.5 was not edited.
- No surviving equation, constant, hypothesis, conclusion, proof step, citation, or bibliography entry was altered or removed. The only removed display was the auxiliary inequality contained inside the explicitly deleted Remark 2.3.
- The AI declaration is byte-identical to the immediately prior source paragraph.
- No Lean source, verification certificate, GitHub state, or Zenodo state was changed.

## Validation

- The theorem-statement checker extracted 16 statement blocks before and after the pass. Both normalized sets have SHA-256 `f55a0f9b4411c3812c95348311637374aba4a8cfed8fb5ccd67edb9e58dba0f8`; result: `PASS_IDENTICAL`.
- The complete Lemma 4.5 statement and proof text is byte-identical before and after the pass. SHA-256: `b8d434266d37f82a47c30ad6f9388f0c8ff2190b8537d919a493538b6c56a2d6`.
- All eight bibliography entries and the complete citation multiset are identical.
- `rem:restriction` occurs zero times after deletion; there is no dangling reference.
- The public repository URL occurs exactly once in the manuscript and exactly once in the supplement.
- The phrases “saturated rotation instances,” “human proof,” “human mathematics,” and “human statements” are absent from both revised sources.
- Manuscript: pdfLaTeX run twice; final log has zero LaTeX errors and zero unresolved references.
- Supplement: pdfLaTeX run twice; final log has zero LaTeX errors and zero unresolved references.
- All 11 manuscript pages and all 4 supplement pages were rendered and visually inspected. No clipping, overlap, broken URL, malformed glyph, or abnormal page break was found.

## PDF metadata

| PDF | Title | Author |
|---|---|---|
| Manuscript | Small Rotation Blocks and the Order-Six Stable Marriage Problem | Myunglae Jo |
| Supplement | Supplementary Material: Formalization Scope and Explicit-Example Checks | Myunglae Jo |

## Page counts

- Manuscript: 11 before, 11 after.
- Supplement: 4 before, 4 after.

## Final SHA-256 hashes

| Artifact | SHA-256 |
|---|---|
| `public_repo/paper/f6_core_v08.tex` | `34a9d084440f2828a25141f28dffba252620f204142133cf76647d9a4d2fb9e9` |
| `public_repo/paper/SUPPLEMENTARY_MATERIAL_V08.tex` | `ce6372530476bf74ac1ed7f4b0dc8ef2796f38ae10213ffc2ba00ff9fc30c7de` |
| `public_repo/paper/MANUSCRIPT.pdf` | `9836990bd64bb6a4ed752ffedc60a770d1216715785872741c3be764b12525ae` |
| `public_repo/paper/SUPPLEMENTARY_MATERIAL.pdf` | `f683aaf1b5c7290ce0725a89a7866acde03d718fc4c59966afcf3c6db7c4299f` |

## Remaining release actions

The local micro-editorial pass is complete. Public GitHub synchronization and Zenodo update/publication remain intentionally deferred.
