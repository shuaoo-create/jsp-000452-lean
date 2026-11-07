import PaidWholeCoreSuccessors
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Every genuine smaller complete row inherits the same positive matching
deficit; testing the empty first color forces the length bounds. -/
theorem paid_erased_row_length_bounds {X : Type u} [Finite X] (G : SimpleGraph X) (A : Set X)
    {s t : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (r N d : ℕ) (pos : 0<d)
    (actual : PaidErasedCoreRow G A n m r N d) :
    r+d+1≤min s t ∧ max s t≤matchingEdges (eraseInternal G A) := by
  let Z := eraseInternal G A
  obtain ⟨row,_,eq,_⟩ := actual
  let R := (⊥ : SimpleGraph X)
  have cost : matchingEdges R+matchingEdges (Z \ R)+d=rowCount s t r := by
    change matchingEdges (⊥ : SimpleGraph X)+matchingEdges (Z \ ⊥)+d=_
    rw [matchingEdges_bot,sdiff_bot,Nat.zero_add];exact eq.symm
  have res := forcing_row_strong_lengths_of_coloring Z hs ht (padDemand n) (padDemand m)
    (pad_positive n pn) (pad_positive m pm) row R bot_le d pos cost (by
      change matchingEdges (⊥ : SimpleGraph X)<min s t;rw [matchingEdges_bot];exact lt_min hs ht)
  change matchingEdges (⊥ : SimpleGraph X)+r+d+1≤min s t ∧ max s t≤matchingEdges (Z \ ⊥) at res
  simpa only [matchingEdges_bot,Nat.zero_add,sdiff_bot] using res

/-- With μ<t, the actual edge-erased row forces t≥μ+r+d+1. The symmetric
conclusion holds when μ<s, without changing the chosen original region. -/
theorem strict_source_erased_tail_lengths (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let μ := matchingEdges (F.G.induce K.core)
    let d := F.rank-matchingEdges F.G
    (μ<F.t → μ+F.r+d+1≤F.t) ∧ (μ<F.s → μ+F.r+d+1≤F.s) := by
  intro μ d
  obtain ⟨_,_,blue,red⟩ := strict_source_paid_erased_core_successors F paid K
  have two := (minimal_strict_source_deficit F paid).2.2
  change 2≤d at two
  constructor
  · intro live
    have lengths := (paid_erased_row_length_bounds F.G K.core F.hs (by omega : 0<F.t-μ) F.n
      (remainingDemand F.m μ) F.pn (remainingDemand_positive F.m F.pm μ) F.r F.rank d (by omega) (blue live)).1
    have short := (le_min_iff.mp lengths).2;omega
  · intro live
    have lengths := (paid_erased_row_length_bounds F.G K.core (by omega : 0<F.s-μ) F.ht (remainingDemand F.n μ)
      F.m (remainingDemand_positive F.n F.pn μ) F.pm F.r F.rank d (by omega) (red live)).1
    have short := (le_min_iff.mp lengths).1;omega

#print axioms paid_erased_row_length_bounds
#print axioms strict_source_erased_tail_lengths
end JSP452Audit.StarHost
