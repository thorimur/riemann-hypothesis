# Verification notes

Everything in this folder was written by the people checking the submission, not by its author.
Comparator's output will be added here when the run finishes.

## Source

| Item | Value |
|---|---|
| Announcement | <https://alpo.ge/remark.pdf>, sha256 `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d` |
| Archive | `https://alpo.ge/lean.tar.gz.part01` … `part14`, downloaded 2026-11-20 |
| Joined archive | `cat lean.tar.gz.part{01..14} > lean.tar.gz`: 239,275,554 bytes, sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` |

The first commit of this repository, `40e56bab`, is the archive's `lean/` directory exactly as
published. Later commits add only `src/Challenge.lean`, `comparator.json`, `export-targets.txt`, a marked
block at the end of `lakefile.toml` that registers the `Challenge` library, the README, this folder and the CI
workflow. `git diff 40e56bab HEAD --stat` shows this, and CI downloads the archive again and
compares it with the tree.

The server answers HTTP 200 with an HTML page for any path, so a `part15` URL appears to exist.
Check the joined sha256, not the status codes.

## Size

175,187 `.lean` files and 1,030,531,854 bytes of source: 17,374,215 lines, of which 15,531,759
are non-blank. There are no comments. The source has 818,755 `theorem`/`lemma` declarations and
242,067 `def`/`abbrev`/`structure`/`class`/`instance`/`inductive` declarations. Every file is in
the import closure of `Main`.

| Library | Files | Lines |
|---|---:|---:|
| Development | 141,928 | 12,232,663 |
| Formalism | 18,254 | 3,200,748 |
| GroundTheory | 8,507 | 1,119,138 |
| ReciprocityTheory | 3,845 | 563,016 |
| CompanionTheory | 2,027 | 194,218 |
| PositivityTheory | 449 | 55,130 |
| Lemmata | 167 | 9,232 |
| Supplements, BuildAid, `Main.lean`, `Statements.lean` | 10 | 70 |

## Static scan

[`static-scan.txt`](static-scan.txt) is a text search over every file. It finds no `axiom`,
`sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `debug.*`
option or `skipKernelTC`. All notation is `local` or `scoped`. The two uses of metaprogramming:

- `BuildAid/D1.lean` … `D5.lean` each add one name to Lean's deny list for library suggestions.
- `Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean` copies declarations
  under new names with `addDecl`, so the kernel checks every copy.

A text search is not a proof. The axiom check and kernel replay in Comparator are.

## Statements

`Main.lean` proves `riemannHypothesis` as `Formalism.VW.rh_of_every allChi`, where `allChi` says
that no Dirichlet L-function vanishes for Re s > 1/2. The step from that to RH and to the
critical-line statements (`Formalism/GammaFactorNonvanishing/CritLine.lean`) is the standard
functional-equation argument, using Mathlib's lemmas.

The statements were read by hand:

- Mathlib's `RiemannHypothesis` excludes the trivial zeros −2(n+1) and the point s = 1, where
  Mathlib's `riemannZeta` has a junk value.
- The Dirichlet statements quantify over every modulus and every character, imprimitive ones
  included. The extra Euler factors of an imprimitive character vanish only on Re s = 0, which
  the hypotheses exclude.
- Every `1 / 2` is compared with `s.re`, so it is real division.
- Dedekind zeta functions and other L-functions are not covered.

## Dependencies

Each pin in `lake-manifest.json` was compared with its repository on GitHub.

| Package | Pin | Result |
|---|---|---|
| mathlib | `0df444a360ea` | tag `v4.33.1`: one commit on top of `db584cd6d46c` (tag `v4.33.0`, on `master`) that changes only `lean-toolchain` |
| plausible | `b7eb3304aeae` | on `main` |
| LeanSearchClient | `5f4d51b81cbd` | on `main` |
| importGraph | `16f02aa76428` | on `main` |
| proofwidgets | `4be2e3d5087e` | on `main` |
| aesop | `3448c0bcc5ce` | on `master` |
| Qq | `92c15be17b7c` | on `master` |
| batteries | `4488d40d070b` | on `main` |
| Cli | `6130a47896ce` | on `main` |

To repeat the Mathlib check: `git diff --stat db584cd6d46c 0df444a360ea` in a Mathlib clone shows
only `lean-toolchain`, and `git merge-base --is-ancestor db584cd6d46c origin/master` succeeds.

## Lean version

The project is pinned to Lean `v4.33.1` (2026-08-21). Where that sits among this year's kernel
fixes, from Lean's release notes and issue tracker:

- **Included.** The fix for [#14576](https://github.com/leanprover/lean4/issues/14576)
  (wrong-structure projections giving an axiom-free proof of `False`; fixed in 4.32.2 and
  4.33.0), the other kernel soundness fixes of 4.33.0, and the fixes 4.33.1 itself backported:
  the `is_def_eq` cache (#14806), `is_prop` (#14807), non-uniform inductive occurrences
  (#14582), a reference-count overflow that could become a use-after-free in the kernel
  (#14838), and the requirement of GMP 6.3.0 (#14833).
- **Not included.** The runtime fixes of 4.34.1: #15241 and #15289, which the release notes say
  could potentially be turned into a proof of `False` in the official kernel with deliberately
  constructed input, and #15288. The notes say kernels not built on the Lean runtime are
  unaffected. Also not included: the `leanchecker` fixes #15100 and #15101, and #16489, which was
  fixed one day after 4.36.0.

For this reason a pass by the 4.33.1 kernel alone, which is what a successful build is, counts
as limited evidence here. The judging is done by Lean 4.36.0 and independent checkers.

## Tools

| Tool | Revision | Role |
|---|---|---|
| Lean `v4.33.1` | official release | builds the project |
| [lean4export](https://github.com/leanprover/lean4export) | tag `v4.33.0` (`15f6055e`), built with Lean `v4.33.1` | writes the two exports |
| Lean `v4.36.0` | official release | `lake comparator`, its kernel, and the bundled `leanchecker-paranoid`, `nanoda_bin`, `con-leche`, `con-ron` |
| bubblewrap | Debian `0.12.0` | the sandbox `lake comparator` requires |
| [lean4lean](https://github.com/digama0/lean4lean) | `master` (`67f63b0c`), built with Lean `v4.33.1` | sixth checker, run separately |

lean4export carries a `v4.33.0` toolchain file. It is built with `v4.33.1` because Lean refuses
`.olean` files written by a different Lean build, and it has to read the project's. Both Lean
toolchains on our machine were compared file by file with the official release archives.

## Smoke test

Before the real run, the route in the README was tested on a Mathlib-sized example: a solution
on Lean `v4.33.1` and the same Mathlib pin, proving four small statements (`zeta_two`,
`zeta_ne_zero`, `exp_pos'` and `sqrt_two_irrational`). Its export has 54,461 declarations and is 371 MB.

| Checker (Lean `v4.36.0`) | Verdict | Time | Peak memory |
|---|---|---|---|
| Lean kernel | accepts | 70 s | 0.75 GB |
| Lean paranoid (`leanchecker-paranoid`) | accepts | 81 s | 0.78 GB |
| nanoda | accepts | 14 s | 0.41 GB |
| con-leche | accepts | 15 s | 1.05 GB |
| con-ron | accepts | 27 s | 1.47 GB |
| lean4lean (only with `--paranoid`) | rejects: `unknown constant 'Decidable.intro'` | 11 s | 0.68 GB |

With the four checkers named in the config, `lake comparator` exits 0 with "Your solution is
okay!". With `--paranoid` it exits 1, on lean4lean alone. On a small test project, a wrong
statement, a `sorry` and an extra axiom were each rejected before any kernel ran, and a proof
swapped inside the export was rejected by every kernel.

## lean4lean

`lake comparator --paranoid` runs the four checkers named in `comparator.json` plus lean4lean.
Lean 4.36's lean4lean rejects every export made by Lean 4.33.1 with
`unknown constant 'Decidable.intro'`, because 4.36 redefined `Decidable` in the core library.
The flag therefore fails on this project whatever the proof contains. So `comparator.json`
names the other four checkers directly, and lean4lean `master` is built with Lean `v4.33.1`
and replays the compiled `.olean` files:

```bash
lake env lean4lean --fresh Main
```

This checker reads the build's output files, not the export the other five judge.
On the Mathlib-sized smoke test it accepted all 750,225 declarations it replayed, in 37 minutes
on one thread.

## Sandbox

- **Build.** The build runs in a rootless podman container with no network, a read-only root
  filesystem, all capabilities dropped, and the Lean toolchain mounted read-only:

  ```bash
  nice -n 10 podman run --rm -i --network none --read-only --tmpfs /tmp:rw,size=64g \
    --userns=keep-id --security-opt no-new-privileges --cap-drop all --memory 440g \
    -v "$WORK":"$WORK":rw \
    -v "$HOME/.elan/toolchains/leanprover--lean4---v4.33.1":/opt/lean:ro \
    -e HOME=/tmp/home -e PATH=/opt/lean/bin:/usr/bin:/bin \
    -w "$WORK/proj/lean" --name rhcheck-build \
    rhcheck-sandbox:1 bash -c 'mkdir -p $HOME; lake build Main'
  ```

  `rhcheck-sandbox:1` is `debian:trixie-slim` plus `git`, `ca-certificates` and `procps`.
- **What the build could reach.** Compiling the submission runs its code. In our run the
  container could write to the whole work directory, which holds the compiled Mathlib, the
  exporter and scratch projects. It could not see the Lean `v4.36.0` toolchain that judges, and
  the `v4.33.1` toolchain was read-only. Three things follow from that:
  - The challenge export given to the judge is made in a new folder, created after the
    container has exited, from a fresh clone and a fresh download of Mathlib's official cache.
    A build that altered the compiled Mathlib in its own folder cannot change what the
    challenge means. CI's `challenge-export` artifact is a second, independent copy.
  - The exporter and the other tools in the work directory are rebuilt after the build.
  - Every compiled dependency file in the build folder is compared with a clean official copy.
    A first comparison during the build found all 121,742 files identical.
- **Export.** The solution is exported inside a sandbox as well, with no network and the build
  folder read-only. The exporter maps the build's `.olean` files straight into memory, and
  `lake env` reads the folder's configuration, so both steps handle files the build could have
  written. Only the export file leaves the sandbox, and the judge treats it as untrusted.
- **After the build.** Nothing in the build folder is run or opened outside a sandbox. The
  judge's config, the export targets and the challenge export come from the clean clone.
- **Judge.** `lake comparator` runs the checkers inside its own bubblewrap sandbox, with no
  network. Since it is given exports, it builds nothing from the project.
- **Standalone Comparator.** The archived standalone Comparator (tag `v4.33.0`) is the
  fallback. Its documented sandbox, landrun under `systemd-run`, left two gaps on Linux 6.12:
  landrun cannot restrict UDP before Linux 7.2, so DNS lookups and UDP sends succeeded, and the
  build could read the whole home directory. Running it with `PrivateNetwork=yes` and
  `ProtectHome=tmpfs` closes both.

## Building

- On our machine (48 cores, 503 GB of RAM) the build is on course for 7 to 10 hours.
- Lake writes a `.setup.json` file per module that lists the module's whole import closure. In
  this project they average about 6 MB, which over 175,187 modules is around a terabyte. A
  module's file is not needed once the module is built, and deleting it leaves the build up to
  date. Run this beside the build:

  ```bash
  while sleep 120; do
    find .lake/build/ir -name '*.setup.json' | while IFS= read -r f; do
      t=".lake/build/lib/lean/${f#.lake/build/ir/}"
      [ "${t%.setup.json}.trace" -nt "$f" ] && rm -f "$f"
    done
  done
  ```

- Estimates for the real run, scaled from the smoke test and uncertain by a factor of 2 to 3:
  about 3.2 million declarations, a solution export of 70 to 75 GB, and about 12 hours for the
  five checkers in sequence, with a peak of roughly 285 GB of memory in con-ron.

## Published oleans

A third party publishes compiled `.olean` files for every module at
<https://proofsandreasons.io/rh-oleans.html>, with the SHA-256 of each one. They were built with
a bare `lean <file> -o <olean> --setup <json>` per module, not with Lake, so they have no Lake
trace files and Lake treats them as out of date. Checked on 2026-11-20:

- They were built from this repository's source: the page gives the same joined-archive sha256 as
  above.
- Their dependency files (Mathlib, Batteries, Aesop, Qq, ProofWidgets, importGraph, plausible,
  LeanSearchClient) are byte-identical to Mathlib's official cache for the pinned commit.
- `Formalism.SuccessiveMinima` (15 modules) was rebuilt on macOS (arm64) with the same Lean
  `v4.33.1` release. 11 oleans match the published hashes. The other 4 differ only in a file path.

**Why the 4 differ.** Lean `v4.33.1` writes every linter warning a module emits into its olean
through the `lintLogExt` extension (`src/Lean/Linter/PersistentLintLog.lean`). Each entry
records the source file name exactly as it was passed to `lean`. The 4 modules are the ones in
the sample that emit linter warnings (deprecations, `haveI`, unused section variables). The
recorded path depends on the build:

| Build | Path in the olean |
|---|---|
| published | `/mnt/data/sdedeo/alp/work/lean/src/…` |
| `lake build` | the absolute path of the checkout's `src/…` |
| the published bare command, run from the checkout | `src/…` |

Two checks show the path is the only difference. With the publisher's prefix replaced by `src/`,
the published oleans and the bare-command rebuild contain the same strings. Each published file
is also 32 bytes larger: the 31 extra characters of the path, padded to 8-byte alignment. That
is strong evidence but not a structural comparison. Rebuilds are otherwise deterministic: repeated
runs, and runs with `-j1` and `-j4`, give identical files.

So **an olean's hash depends on the build directory whenever the module emits a linter warning.**
Comparing hashes across machines confirms only warning-free modules unless both builds pass the
same path. The published oleans also record the builder's directory layout.

## Limits

- Comparator checks the challenge and the solution against the same Mathlib, so it cannot
  detect a modified Mathlib. The pin here is Mathlib's official `v4.33.1` tag, and the
  challenge export is reproduced on GitHub's CI.
- The exports are made by Lean 4.33.1 and judged by Lean 4.36.0. Lean's help text lists exports
  made elsewhere as an intended use, and the export format version is the same (3.1.0), but
  this is not the common path.
- A passing run still trusts the checkers, Mathlib's definitions, Mathlib's official build
  cache, the exporter, and the sandboxes.

## Results

The build is in progress. The exports' checksums, Comparator's output, the exact command lines
and the machine details will be added to this folder.
