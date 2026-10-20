# Chemical heredity without genetic templates

Acquisition and retention of catalytic function are established for a four-compartment chemical model with three prescribed catalyst types and finite resources. Starting with at least 512 copies of each of two old catalyst types per compartment, arbitrary candidate counts and arbitrary fuel occupancy, a seeding phase ends at time 30. At the fixed beta = 4,000,000 operating point, the joint mission through time 60 has failure probability at most 0.004517975690072193. It includes applicable count floors of 16 for both actual complementary daughters, 3,000,000 service credits, at least five initiating divisions per compartment after seed withdrawal, and eleven current-population recoveries interleaved with ten selected actual divisions by time 55.5. Seven simultaneous resource ceilings are enforced by one finite-stock process, with the first attempted excess entering failure. The proof connects the marked physical-time law, deterministic seed withdrawal, stopped recovery and resource accounting to the complete mission.

The main theorem is `P161Formal.template_free_heredity_finite_stock`. Its initial hypothesis requires at least 512 copies of each old catalyst type at every site. Candidate counts and fuel occupancy are arbitrary within the state space. Failure of the joint mission has probability at most 4517975690072193/10^18.

The mission protects applicable counts at 16, including both actual complementary daughters, and guarantees 500 service credits per required coordinate in every fixed 0.1 window through time 60. The resulting service total is 3000000 credits. It also gives at least five initiating divisions per compartment after time 30 and eleven first current-population Ready512 recoveries interleaved with ten strictly later first actual divisions by 55.5. Each recovery takes at most 0.5 and each selected division wait at most 2. The service horizon remains 60.

| Gross resource ledger | Ceiling |
|---|---:|
| Accepted feed entries | 800000000 |
| Catalyst seed entries | 5000 |
| Consumed fuel, including discarded victim fuel | 800000004 |
| Birth-plus-seed precursors | 800005004 |
| Complete division operations | 1200 |
| Catalyst-position handling in overwritten compartments | 7372800 |
| Discarded victim fuel, already charged in gross supply | 1200 |

The clock law retains complete marks and actual holding times. Both phases are sampled without conditioning on success. One stock allocation runs through the entire mission; the first attempted excess enters absorbing failure, with equality at a ceiling permitted. The realization retains driving history as auxiliary randomness, while physical observations read the stopped stock trace.

`Challenge.lean` independently defines the model, law and mission using only the pinned Mathlib and Lean libraries. `Solution.lean` imports the substantive proof development supplied here. The Comparator configuration contains one flagship and 48 proof-construction or numeric obligations, with no substantive definition holes. Module names and the exact scientific source bytes are preserved in the source manifest.

The selected result is Theorem 1 of [Chemical heredity without genetic templates](paper/Chemical_Heredity_Without_Genetic_Templates.pdf). The accompanying [Supplement S1](paper/Supplement_S1.zip) contains the finite data, exact-arithmetic verifier and mathematical source records. The manuscript’s restoration theorem and other operating comparisons retain their conventional proofs. See `PROVENANCE.md` for the statement correspondence.

Reproduction uses Lean 4.35.0-rc2 and Mathlib commit 065356127b1dc0016f66b7283ce0ce2c4055aa55, with the complete manifest supplied. After installing those pinned dependencies, the standard targets are `lake build Solution` and `lake comparator --config comparator.json`; the standard Comparator requires Linux and bubblewrap. Launch compiler work under the host's finite resource supervisor. `scripts/reproduce.py` validates source hashes by default and requires an explicit supervisor prefix for fresh checks. `--build-only` supports a fresh Windows Solution build; `--build` also invokes the standard Linux Comparator. The recorded local native comparison used the separately documented adapter. Receipts distinguish reused strict artifacts, fresh comparison and individual kernel checks.
