# Handover Notes for New Chat Session
# Pedigree Polytopes Lean 4 Project
# T.S. Arthanari, University of Auckland
# Generated: May 2026

---

## CRITICAL FILES ON DISK

### Lean 4 Project
- Location: C:\Users\tarth\Membership_Project\
- GitHub: https://github.com/TiruArt/Pedigree-Polytopes-Lean4
- Build: lake build MembershipProject.Core.N_PEqualsNP
- Result: Build completed successfully (2968 jobs)
- theorem p_equals_np : P_class = NP_class ✅ PROVED

### arXiv Paper 3 (IN PREPARATION)
- File: arXiv_v3_main.tex (in outputs, push to GitHub)
- Title: A Strongly Polynomial Algorithm for Membership in the
         Pedigree Polytope, with Lean 4 Machine-Verified Consequences
- Status: ~1616 lines, compiling clean in Overleaf (5 minor warnings)
- NOT yet submitted to arXiv — needs final read and Chapter 8 addition

### Paper Inventory
- Paper 1: arXiv:2507.09069 (published July 2025)
           "On the Importance of Studying..."
- Paper 2: Math. Programming submission — DESK REJECTED, not published
- Paper 3: arXiv_v3_main.tex — new submission in preparation

---

## LEAN 4 CHAIN STATUS

All 36 Core files clean. Key files:
- N_RigidCardinality.lean: CordinalityR bound = tau_k - k + 4 ✅
- N_Complexity.lean: O(n^14), all hdim use tau n - (k-3) ✅
- N_FullDimensional.lean: fullDimensional_An ✅
- N_Sufficiency.lean: theorem sufficiency only (no main_ns_theorem) ✅
- N_MembershipCharacterisation.lean: main_ns_theorem, 1 axiom ✅
- N_SupportConcepts.lean: instant flow defs ✅
- N_PEqualsNP.lean: theorem p_equals_np ✅
- N_PedigreeRepresentations.lean: 5 representations ✅
- N_UptoF5.lean: F4, N4, N4(L), F5 visualization ✅
- Backup/N_Necessity.lean: 16 sorries (future work)

AXIOMS (6): tardos_strongly_polynomial, maurras_separation,
            gls_optimisation, cook_np_completeness,
            karp_stsp_np_complete, rao_1976_theorem1

---

## KEY MATHEMATICAL CORRECTIONS
- CordinalityR: tau_k - k + 3 → tau_k - k + 4 (book Corollary 6.1)
- cardinalitytheorem hdim: tau n - (k-2) → tau n - (k-3)
- Tardos reference: Operations Research 34(2) 1986 (not Combinatorica)
- STSP: decision problem NP-complete (Karp); optimisation in P (our result)
- MI-formulation: Chapter 3 (not Chapter 7)

---

## PAPER 3 STATUS

Sections:
1. Introduction (with algorithmic heritage paragraph — NEW)
2. Preliminaries (with network flow / combinatorial LP subsection — NEW)
3. MI-Formulation and Pedigree Polytope
4. Construction of Layered Network
5. Sufficient Condition for Non-Membership
6. Multicommodity Flow and Membership Characterisation
7. Computational Complexity
8. Membership, Separation, and Optimisation (GLS, Maurras — NEW)
9. Properties of conv(A_n) and P=NP Consequence (NEW)
10. Lean 4 Machine Verification and P=NP (with intro for non-specialists)
11. Concluding Remarks
Appendix A: Supporting Results
Appendix B: FFF Algorithm
Acknowledgements: DeepSeek, Claude, Gemini (with trademark symbols)

PENDING: Addition 3 — algebraic topology (needs Chapter 8)
PENDING: Final read-through by Prof. Tiru
PENDING: arXiv submission

---

## KNUTH LETTER PACKAGE (ready to post after arXiv number)
- Letter: Letter_to_Knuth_v2.md (outputs folder)
- Enclosure 1: Enclosure1_N_PEqualsNP.pdf
- Enclosure 2: Enclosure2_arXiv_Abstract.pdf
  (UPDATE with arXiv number once Paper 3 is submitted)

---

## PYTHON PACKAGE
- Package: checking4membership on TestPyPI
- Runner: m3p_runner.py (in project root)
- Tests: n=5 uniform PASS, negative FAIL, pedigree vertex PASS, n=6 PASS
- Full MCF check: pending (main() reads .txt format)
- Input format: sparse (see prob_in_7_1.txt for example)

---

## OUTREACH EMAILS (not yet sent)
- Draft: Cover_Letter_PvsNP.md (outputs folder)
- Priority contacts:
  Cook: sacook@cs.toronto.edu
  Karp: karp@cs.berkeley.edu
  Tardos: eva@cs.cornell.edu
  Schrijver: lex@cwi.nl
  Buzzard: k.buzzard@imperial.ac.uk
  Aaronson: scott@scottaaronson.com

---

## MDPI PAPER (invited, APC waived by Prof. David Carfi)
- Title: From Scepticism to Verification: AI, Lean 4, and the
         Transformation of the Publishing Game in Mathematics
- Journal: Mathematics (MDPI), Special Issue: AI in Game Theory
- Abstract: submitted to Prof. Carfi
- Status: Outline agreed, full paper not yet drafted

---

## KEY LEAN 4 PATTERNS (for reference)
- revert a b before induction: ensures ihm quantifies over all a,b
- hm'_eq : m'+1-1 = m' already in context — add to simp
- Nat.add_sub_cancel — for m'+1-1 in simp
- omega after rw [hm'_eq] at hndm
- ▸ preferred over rw to avoid Eq.mpr cast issues
- split_ifs without with when branch hypothesis unused
- Nat.pow_le_pow_right for k^3 ≤ k^5 bounds