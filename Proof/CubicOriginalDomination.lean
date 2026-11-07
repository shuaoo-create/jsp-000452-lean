import CubicDominationPortProjection
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem cross_transfer (G : SimpleGraph X) (T B A C : Set X)
    (land : ∀v∈T,∀w∈B,G.Adj v w → v∈A ∧ w∈C) :
    crossCount G T B≤crossCount G A C := by
  let L := {p : (↥T × ↥B) // G.Adj p.1.val p.2.val}
  let R := {p : (↥A × ↥C) // G.Adj p.1.val p.2.val}
  have inc (p:L) := land _ p.val.1.property _ p.val.2.property p.property
  let f (p:L) : R := ⟨(⟨p.val.1.val,(inc p).1⟩,⟨p.val.2.val,(inc p).2⟩),p.property⟩
  apply Nat.card_le_card_of_injective f
  intro p q eq
  exact Subtype.ext (Prod.ext (Subtype.ext (congrArg (fun v:R => v.val.1.val) eq))
    (Subtype.ext (congrArg (fun v:R => v.val.2.val) eq)))

private theorem cross_budget_split (G : SimpleGraph X) (A B S : Set X) (sub : S⊆B) :
    crossCount G A (B\S)+crossCount G S A=crossCount G A B := by
  classical
  let _ := Fintype.ofFinite A
  rw [crossCount_swap G S A]
  simp only [crossCount_eq_neighbor_sum]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl;intro v _
  let N := G.neighborSet v.val
  have eq : (N∩(B\S))∪(N∩S)=N∩B := by rw [←Set.inter_union_distrib_left,Set.sdiff_union_of_subset sub]
  have dis : Disjoint (N∩(B\S)) (N∩S) := Set.disjoint_left.mpr (fun _ h hs => h.2.2 hs.2)
  exact ((Set.ncard_union_eq dis).symm.trans (congrArg Set.ncard eq))

/-- A full-degree dominating set of the actual cubic host, with the
bounded-degree projection and the exterior independent set on the same graph. -/
theorem cubic_original_dominating_set (G : SimpleGraph X) (K : DegreeRegion G 3)
    (cap : ∀v,Nat.card (G.neighborSet v)≤3) :
    ∃P:Set X,(∀v,Nat.card (G.neighborSet v)=3 → v∈P ∨ ∃w∈P,G.Adj v w) ∧
      10*P.ncard≤8*(K.roots.ncard+matchingEdges (G.induce K.core))+4*minimumExposure G 3+
        5*((G.induce K.rest).edgeSet.ncard-matchingEdges (G.induce K.rest))+5*crossCount G K.roots K.rest := by
  classical
  let Y := K.core∪K.roots
  let B := K.rest
  let A := K.roots
  obtain ⟨ap,ab,pb,all⟩ := region_partition G K.barrier K.pieces
  change Disjoint A K.core at ap
  change Disjoint A B at ab
  change Disjoint K.core B at pb
  change (A∪K.core)∪B=Set.univ at all
  have cover : Y∪B=Set.univ := by rwa [Set.union_comm A K.core] at all
  have dis : Disjoint Y B := Set.disjoint_union_left.mpr ⟨pb,ab⟩
  have split := (core_rest_partition G K.barrier K.pieces).2.2
  obtain ⟨S,inside,full,ind,dom⟩ := choose_full_exterior_independent G B 3
  have boundary (v:X) (hv:v∈S) (w:X) (e:G.Adj v w) : w∈B ∨ w∈A := by
    rcases (show w∈Y∪B from cover.symm ▸ Set.mem_univ w) with (core|root)|rest
    · exact (split core (inside hv) e.symm).elim
    · exact Or.inr root
    · exact Or.inl rest
  have external := exterior_independent_degree_price G B A S ab.symm inside ind 3 (by decide) full boundary
  let T := {v | v∈Y ∧ Nat.card (G.neighborSet v)=3 ∧ v∉S ∧ ∀w∈S,¬G.Adj v w}
  obtain ⟨P,hit,fee⟩ := cubic_dominates_via_actual_ports G Y B T dis cover (fun _ h => h.1)
    (fun _ h => h.2.1) cap
  have transfer := cross_transfer G T B A (B\S) (by
    intro v hv w wb e
    refine ⟨hv.1.resolve_left (fun hp => split hp wb e),wb,fun ws => hv.2.2.2 w ws e⟩)
  have budget := cross_budget_split G A B S inside
  have cross : crossCount G T B+crossCount G S A≤crossCount G A B := by omega
  have size : Y.ncard=2*(A.ncard+matchingEdges (G.induce K.core))+minimumExposure G 3 := by
    change (K.core∪A).ncard=_
    rw [Set.ncard_union_eq ap.symm,K.core_order];dsimp [A];omega
  change 2*S.ncard≤(G.induce B).edgeSet.ncard-matchingEdges (G.induce B)+crossCount G S A at external
  refine ⟨P∪S,?_,?_⟩
  · intro v vd
    rcases (show v∈Y∪B from cover.symm ▸ Set.mem_univ v) with vy|vb
    · by_cases yes : v∈S
      · exact Or.inl (Or.inr yes)
      by_cases next : ∃w∈S,G.Adj v w
      · obtain ⟨w,ws,e⟩ := next;exact Or.inr ⟨w,Or.inr ws,e⟩
      have vT : v∈T := ⟨vy,vd,yes,fun w ws e => next ⟨w,ws,e⟩⟩
      rcases hit v vT with p|⟨w,wp,e⟩
      · exact Or.inl (Or.inl p)
      · exact Or.inr ⟨w,Or.inl wp,e⟩
    · rcases dom v vb vd with vs|⟨w,ws,e⟩
      · exact Or.inl (Or.inr vs)
      · exact Or.inr ⟨w,Or.inr ws,e⟩
  · rw [size] at fee
    have join := Set.ncard_union_le P S
    change 10*(P∪S).ncard≤8*(A.ncard+matchingEdges (G.induce K.core))+4*minimumExposure G 3+
      5*((G.induce B).edgeSet.ncard-matchingEdges (G.induce B))+5*crossCount G A B
    omega

#print axioms cubic_original_dominating_set
end JSP452Audit.StarHost
