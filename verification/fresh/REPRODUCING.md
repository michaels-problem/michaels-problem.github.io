# Reproducing the checks

This guide describes how to repeat the checks. Read the accompanying report
and its underlying records for the result of the recorded run.

The two Python helpers included here are convenience tools. They were syntax
and help tested only; `portable-compile.py` was not used for the recorded run
and has not been tested by running a complete rebuild. It does not run the
kernel replay or the final audits. Python 3.10 or later is sufficient.

## Check the downloaded files

Keep the public evidence package separate from a new build directory. For
example:

```text
public-evidence/
  REPRODUCING.md
  portable-compile.py
  verify-public-copies.py
  EVIDENCE_FILES_SHA256.json
  PUBLIC_COPY_MANIFEST.json
  records/evidence/build-plan.json
  records/evidence/dependencies.json
  records/evidence/package-sources/
  records/evidence/FreshVerification.lean
toolchain/
  bin/
  lib/lean/
reproduction/
  source/project/
  source/packages/
```

From the directory containing these three directories, run:

```text
python public-evidence/verify-public-copies.py public-evidence
```

This checks the byte length and SHA-256 of every entry in
`EVIDENCE_FILES_SHA256.json`. The manifest itself is excluded from its own list.
If a separately obtained checksum is available, supply it with
`--expected-manifest-sha256`. Without a separately trusted checksum, changing
both a file and its manifest can evade this integrity check.

`PUBLIC_COPY_MANIFEST.json` records the correspondence between private
originals and public copies. To check its public entries separately, use
`--manifest PUBLIC_COPY_MANIFEST.json`. Their `publicSha256` values identify
the downloadable bytes; original hashes identify the preserved private
records. A public copy cannot establish the contents of an unavailable
original. Neither manifest check validates a Lean proof.

## Assemble the pinned sources and toolchain

1. Extract the separate audited source download into
   `reproduction/source/project/`. Check its 257 exact source/configuration
   files against its `SOURCE_MANIFEST.json`; its explanatory README and
   manifest are derived packaging files. Copy
   `public-evidence/records/evidence/FreshVerification.lean` into that same
   project directory. Its expected source hash is in the build plan. The
   three pinned project configuration files are `lean-toolchain`,
   `lakefile.toml`, and `lake-manifest.json`.
2. Obtain the nine package repositories at the exact URLs and full revisions
   in `records/evidence/dependencies.json`. Export each pinned commit with
   `git archive` into `reproduction/source/packages/<name>/`. Do not use a
   branch tip, update the pins, or copy an existing Lake build. The dependency
   records include the original archive hashes and any symbolic links that
   were materialised as regular files. Apply those listed link conversions,
   then check every file against
   `records/evidence/package-sources/<name>.json` (`path`, `bytes`, `sha256`).
   Compare the file inventory as well as the hashes. Git archive metadata can
   vary; if a newly made archive has different bytes, retain its own hash and
   establish source identity by the extracted file manifests. Do not label
   it as the original archive.
3. Obtain the matching official Lean toolchain and place it in `toolchain/`.
   The pinned release is `leanprover/lean4:v4.34.0-rc2`, commit
   `6a10ac8c22beadecabdbb0919c2b50214762f91d`. Use its compiler,
   `leanchecker`, runtime libraries, and bundled `lib/lean` together. The
   Mathlib revision is `4cbb42e75a050e830b7cf0f2ae748d7644f59cf7`.

A structural Git export command, with values taken from the pin records, is:

```text
git -C <repository> archive --format=tar --output=<package>.tar <full-revision>
```

Extract each archive into its own package directory, retaining the recorded
file bytes. A normal working-tree checkout can introduce line-ending changes;
the manifests will detect them. The public evidence does not include the
dependency archives or the native toolchain. Obtaining these sources and tools is a
separate step, and no setup command in this guide has been run for you.

The retained toolchain is not rebuilt or bootstrapped by this procedure.
Record the hashes of the compiler, checker, runtime libraries, and resolved
toolchain artifacts used locally. Compare them with
`records/evidence/toolchain.json` when using the same native distribution.
Another official platform distribution can have different binary hashes;
report that as a different toolchain binary identity, even when the release
and source commit match. Do not replace its checker with a checker from
another Lean release.

## Compile the fresh imported closure

Start with no `build/` artifacts and no `reproduction-records/` directory.
From `reproduction/`, run:

```text
python ../public-evidence/portable-compile.py --plan ../public-evidence/records/evidence/build-plan.json --toolchain ../toolchain
```

The plan has 3,229 distinct modules: 2,974 non-toolchain library modules,
251 mathematical project modules, and four roots/audits:
`AutomaticContinuity`, `Audit`, `CompletionAudit`, and `FreshVerification`.
This is the imported source closure needed for these checks, not all of
Mathlib or a rebuild of Lean's bundled libraries. The plan's earlier import
parser comparison covers 3,227 entries; two aggregate roots were added to the
final compilation plan.

The helper verifies every planned source hash, rejects compiled artifacts
copied into `source/`, and compiles serially into the new `build/` directory.
The recorded run used two compiler workers; serial scheduling changes the
schedule, not the per-module options:

| Sources | Compiler options |
| --- | --- |
| All planned modules | `-j1 -M6144` |
| Project and Mathlib | additionally `-DautoImplicit=false` |
| Mathlib | additionally `-DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true` |

Each command runs in its package's source root. The only non-toolchain
`LEAN_PATH` entry is the fresh `build/` directory; Lean also uses the matching
toolchain's bundled library. Inherited Lean/Lake/Mathlib environment settings
are cleared. No binary package cache is used. The helper does not resume or
overwrite an earlier local reproduction.

The helper retains native stdout/stderr, real exit codes, source hashes before
and after compilation, compiled-file hashes, and timing records. Its final message
is `SOURCE BUILD COMPLETE`, not a claim that kernel replay or final
verification has passed. Before and after the next stage, use:

```text
python ../public-evidence/portable-compile.py --plan ../public-evidence/records/evidence/build-plan.json --toolchain ../toolchain --check-state
```

This rechecks the local source plan, compiler, compiled-source records, and
recorded artifacts, including each expected `.olean`. It does not check
unlisted files or the identities of the toolchain libraries and other executables.

## Replay and run the final audits

Use the same clean environment and fresh search path as the compilation.
Run from `reproduction/source/project/`, resolving the executables from the
matching toolchain. The required commands are:

```text
leanchecker --fresh --verbose FreshVerification
lean -j1 -M6144 -DautoImplicit=false Audit.lean
lean -j1 -M6144 -DautoImplicit=false CompletionAudit.lean
lean -j1 -M6144 -DautoImplicit=false FreshVerification.lean
```

Here `LEAN_PATH` must resolve to `reproduction/build/` only; inherited package
paths must not remain. Capture each native process's stdout, stderr, exit
code, start/end times, and executable hash. Wait for actual process completion.
A startup message or a process still running is not successful replay. The
pinned checker's relevant flags are `--fresh --verbose`; do not add compiler
flags such as `-j1` or `-M6144` to that checker command.

The official `leanchecker` replays eligible declarations with Lean's kernel;
it is not an independent implementation of the kernel. Its imported
environment includes bundled toolchain declarations as well as the fresh
library and project modules. It skips unsafe declarations and partial
implementation bodies. The expected project audit identifies zero unsafe
declarations and five generated partial compiler helpers; its log lists
those helpers explicitly. Do not report skipped bodies as individually
replayed proofs or convert the audit's environment counts into a checker
per-declaration success counter.

The coverage report describes the environment observed while compiling
`FreshVerification.lean`; its recorded `trustLevel` is 1025. For the separate
`--fresh` replay, the pinned checker creates an empty kernel environment at
trust level 0. This follows from `replayFromFresh` in the pinned
`LeanChecker.lean` and the default argument of `mkEmptyEnvironment` in
`Lean/Environment.lean`.

Require zero native exit codes and these exact audit markers:

```text
PROJECT_AXIOM_AUDIT declarations=3199 theorems=2478 unexpected=0 unsafe=0
THEOREM_A_COMPLETION_AUDIT exactStatement=true universePolymorphic=true unexpected=0 unsafe=0
FRESH_AUDIT_GATES_PASS
```

Read the expanded audit, including `FRESH_EXACT_TARGET`, the target/witness
axiom lists, the project axiom union, and the module coverage records.
`CompletionAudit.lean` checks the original universe-polymorphic
`TheoremAStatement` with no extra assumptions. The permitted transitive
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.

Finally, verify that every resolved non-toolchain import comes from the new
build, every remaining resolved import comes from the matching toolchain,
and that sources, configuration, executables, runtime libraries, and all
resolved artifacts retain their recorded hashes. The recorded run's
`coverage.json`, pre/post replay identity records, and post-replay audit
records show the corresponding checks performed by its original driver.
The portable helper does not automate that entire identity/coverage audit.

Only after compilation, completed kernel replay, these final audits, and the
identity checks all succeed should a reproduction be reported as complete.
The three final audit compilations are additional checks after the 3,229
distinct planned module compilations. Preserve failed or interrupted attempts
and the actual exit codes; do not count an interrupted supervisor as a native
compiler failure unless the native process actually returned that failure.

Freshly produced artifacts, timings, and binary hashes need not equal the
recorded ones across platforms. A reproduction report should identify its
own sources and results rather than copy the earlier run's completion date,
duration, hashes, or outcome.

## Timing of the recorded run

The source build's total wall-clock duration was 14398.249996 seconds,
including an author-requested pause for website work from
2026-09-23T11:52:44.147293+00:00 to 2026-09-23T12:11:57.105347+00:00.
That recorded interval lasted 1152.958054 seconds.
Subtracting only that interval gives 13245.291942 seconds;
this is not CPU time and can include other waits or interruptions. Do not use
either figure as an expected duration for a new reproduction. The timing-only
derivative is `records/execution-pause.json`; its original and public hashes
are distinguished in `PUBLIC_COPY_MANIFEST.json`.
