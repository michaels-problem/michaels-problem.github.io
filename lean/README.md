# Theorem A

This source package proves AutomaticContinuity.theoremA : TheoremAStatement.{u}.

Every character on a complete Hausdorff commutative complex locally multiplicatively convex algebra is bounded on bounded subsets. The algebra may be nonunital and nonmetrisable. No continuity hypothesis is imposed on the character.

The 251 mathematical modules and the three root files are unchanged copies from the checked snapshot. SOURCE_MANIFEST.json records their SHA-256 hashes together with the three pinned configuration files. This README and the manifest were prepared for the website. The source archive has its own hash in the website download manifest.

## Building

Install the Lean version in lean-toolchain and Git. From the extracted source directory, with Elan and Lake available:

    lake exe cache get
    lake build AutomaticContinuity
    lake env lean -j1 -M8192 -DautoImplicit=false Audit.lean
    lake env lean -j1 -M8192 -DautoImplicit=false CompletionAudit.lean

Keep lake-manifest.json unchanged to retain the recorded dependency revisions. These commands describe a normal build using library caches. A separate fresh rebuild of the imported libraries and project, official kernel replay, and final theorem and axiom checks have passed for this source snapshot. The companion website provides the completed report and a separate evidence archive with reproduction instructions. The normal commands above do not repeat that fresh verification. The archive does not include the Lean compiler, compiled artifacts or external library checkouts.

## Proof

Statement.lean contains the target and its four project definitions. TheoremA.lean closes the proof. The required coordinate-flag approximation is proved using compact convex polynomial approximation, holomorphic families, additive Cauchy splitting, finite coordinate cuts and compact exhaustion. The coefficient algebra, Arens interpolation, substitution and unitization then yield Theorem A. This specialised argument does not formalise the general Oka theorems used in the manuscript.

## Attribution

The project-specific Lean development was produced with ChatGPT in Codex under the author's supervision. Alternative proofs were permitted where they preserved the intended theorem. Mathlib and its dependencies retain their own authorship and licences.
