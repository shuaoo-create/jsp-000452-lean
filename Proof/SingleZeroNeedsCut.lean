import SmallPreferredDeletion
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

theorem zero_single_part_requires_bad_cut (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (many : 3≤I.ncard) (D : ℕ) (six : 6≤D) (par : Even D)
    (reg : ∀v,Nat.card (Q.neighborSet v)=D) (crit : PerfectAfterEveryDeletion Q)
    (s : OnePreferredPart Q I) (zero : baseReserve Q D=0) :
    D+1≤s.preferred.ncard ∧ ∃x:s.preferred,¬ExposablePoint (Q.induce s.preferred) x := by
  classical
  have enough : D+1≤s.preferred.ncard := by
    by_contra! short
    have odd := Nat.odd_iff.mp s.odd
    have evenD := Nat.even_iff.mp par
    obtain ⟨U,c,w⟩ := small_single_part_witness Q I ind many D six par reg s (by omega)
    have bound := deletionBudget_le_of_witness Q (D-1) U w
    have present := (Set.ncard_pos (Set.toFinite I)).mp (by omega)
    have eq := ((zero_reserve_independent_cut Q D (by omega) reg crit zero I present ind).2.2
      (D-1) (by omega) (by omega)).2
    omega
  refine ⟨enough,?_⟩
  by_contra! all
  have paid := large_critical_single_part_pays Q I ind largest many D six reg crit s enough all
  omega

/-- A zero-reserve genuine residual partition with only one nontrivial
hole now requires a large preferred union with a nonexposable vertex. -/
theorem actual_single_zero_bad_cut (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (many : 3≤I.ncard) (D : ℕ) (six : 6≤D) (par : Even D)
    (reg : ∀v,Nat.card (Q.neighborSet v)=D) (crit : PerfectAfterEveryDeletion Q)
    (zero : baseReserve Q D=0) (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ)) (gap : N.vertsᶜ.ncard+1=I.ncard)
    (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (p : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))) (big : 3≤(mateBlock (Q.induce Iᶜ) N p.val).ncard)
    (single : ∀j : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X)), j≠p → (mateBlock (Q.induce Iᶜ) N j.val).ncard=1) :
    let B := Subtype.val '' (mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N)
    D+1≤B.ncard ∧ ∃x:B,¬ExposablePoint (Q.induce B) x := by
  intro B
  obtain ⟨s,eq⟩ := actual_single_preferred Q I N hm max gap noEx p big single
  have res := zero_single_part_requires_bad_cut Q I ind largest many D six par reg crit s zero
  change s.preferred=B at eq
  rwa [eq] at res

#print axioms zero_single_part_requires_bad_cut
#print axioms actual_single_zero_bad_cut
end JSP452Audit.StarHost
