# Vendored Lean libraries

Each library keeps its upstream licence and per-file provenance in `provenance/`
(summary: `provenance/THIRD-PARTY.md`). All licences are Apache-2.0.

| Folder | Library | Upstream | Provenance |
|---|---|---|---|
| `openai-math/OAI/Combinatorics/Progressions` | `OAI` (1,043 files) | openai/math `4eaee87548250b2682affda7d05d947c05554bae`, ported to Lean 4.35.0 modules and pruned to the declarations the final proofs need | `provenance/openai-progressions-files.json`, `provenance/openai-progressions-pruning.json` |
| `openai-math/OAI/NumberTheory/SiegelZeros` | `OAI` (201 files) | openai/math `4eaee87548250b2682affda7d05d947c05554bae`, ported to Lean 4.35.0 modules | `provenance/openai-siegelzeros-files.json` |
| `openai-math/OAI/NumberTheory/DirichletL` | `OAI` (1 file, `LogarithmicControl`) | openai/math `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, converted to a Lean module | `provenance/openai-logarithmic-control.json` |
| `carleson/Carleson` | `Carleson` (40 files, 16,130 upstream lines) | fpvandoorn/carleson `52cba54d4b7b444e937c7abbc67835afa2a0bb16`, ported from Lean v4.36.0-rc1 | `provenance/carleson-files.json` |

Licence texts: `openai-math/LICENSE` (openai/math) and
`provenance/third-party-licenses/CARLESON-LICENSE`.

The libraries build with the options of their upstream builds
(`autoImplicit = false`), not this project's linter set; see `lakefile.toml`.

The provenance records list every change made in porting and pruning, file by file, with upstream
and vendored SHA-256 hashes.

Upstream declarations of the Carleson project that contain `sorry` are commented out in the port;
apart from the two intentional placeholders of `Challenge.lean`, no compiled declaration of this
repository uses `sorry`.
