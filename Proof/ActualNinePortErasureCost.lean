import ExactNinePortMatchingPartition
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

noncomputable def portCharge (i : Fin 2) : ℕ := by
  classical
  exact if R.essential i then 1 else 0
noncomputable abbrev portCount := R.portCharge 0 + R.portCharge 1

theorem portPart_edge_count (i : Fin 2) :
    (R.portPart i).edgeSet.ncard=(G.induce (R.box i)).edgeSet.ncard+R.portCharge i := by
  classical
  let B := R.portPart i
  let U := R.box i
  let L := eraseInternal B U
  have inside : B.induce U=G.induce U := by
    ext x y
    exact ⟨fun h => h.1,fun h => R.internal_in_portPart i
      ((portInside_adj G U x.val y.val).mpr ⟨h,x.property,y.property⟩)⟩
  have portOnly {x y : X} (adj : L.Adj x y) : R.essential i ∧
      ((x=(R.port i).tip ∧ y=(R.port i).root) ∨ (y=(R.port i).tip ∧ x=(R.port i).root)) :=
    ((R.portPart_edges i x y).mp adj.1).resolve_left
      (fun h => adj.2 ((portInside_adj G U x y).mp h).2)
  have count : L.edgeSet.ncard=R.portCharge i := by
    by_cases h : R.essential i
    · rw [portCharge,if_pos h,Set.ncard_eq_one]
      let edge := s((R.port i).tip,(R.port i).root)
      refine ⟨edge,Set.Subset.antisymm ?_ ?_⟩
      · intro z hz
        induction z using Sym2.inductionOn with
        | _ x y =>
          rcases (portOnly (show L.Adj x y from hz)).2 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          · exact Set.mem_singleton _
          · exact Set.mem_singleton_iff.mpr Sym2.eq_swap
      · apply Set.singleton_subset_iff.mpr
        exact (show L.Adj (R.port i).tip (R.port i).root from
          ⟨⟨(R.port i).edge,Or.inl ((R.tip_reserved_iff i).mpr h)⟩,
            fun both => R.root_outside_box i i both.2⟩)
    · rw [portCharge,if_neg h]
      have empty : L=⊥ := by
        ext x y;exact ⟨fun e => (h (portOnly e).1).elim,False.elim⟩
      rw [empty,SimpleGraph.edgeSet_bot,Set.ncard_empty]
  have all := erase_internal_edge_count B U
  rw [inside] at all
  change B.edgeSet.ncard=L.edgeSet.ncard+(G.induce U).edgeSet.ncard at all
  change B.edgeSet.ncard=(G.induce U).edgeSet.ncard+R.portCharge i
  omega

theorem portParts_disjoint_edges : Disjoint (R.portPart 0).edgeSet (R.portPart 1).edgeSet := by
  apply Set.disjoint_left.mpr
  intro z
  induction z using Sym2.inductionOn with
  | _ x y =>
    intro a b
    have z0 : (R.portPart 0).Adj x y := a
    have z1 : (R.portPart 1).Adj x y := b
    have dis := R.disjoint_boxes
    rcases (R.portPart_edges 0 x y).mp z0 with inner|⟨_,ends⟩
    · obtain ⟨_,hx,hy⟩ := (portInside_adj G _ x y).mp inner
      exact z1.2.elim (fun h => Set.disjoint_left.mp dis hx (R.reserved_subset 1 h))
        (fun h => Set.disjoint_left.mp dis hy (R.reserved_subset 1 h))
    · have tipAway : (R.port 0).tip∉R.box 1 :=
        fun h => Set.disjoint_left.mp dis (R.port 0).tip_mem h
      rcases ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact z1.2.elim (fun h => tipAway (R.reserved_subset 1 h))
          (fun h => R.root_outside_box 0 1 (R.reserved_subset 1 h))
      · exact z1.2.elim (fun h => R.root_outside_box 0 1 (R.reserved_subset 1 h))
          (fun h => tipAway (R.reserved_subset 1 h))

theorem adapted_edge_account (cap : ∀x,Nat.card (G.neighborSet x)≤9) :
    R.portCount≤2 ∧ R.adapted.edgeSet.ncard=9*R.totalCapacity+8+R.portCount ∧
      G.edgeSet.ncard=R.erased.edgeSet.ncard+9*R.totalCapacity+8+R.portCount := by
  classical
  have charge (i : Fin 2) : R.portCharge i≤1 := by unfold portCharge;split <;> omega
  have union : R.adapted.edgeSet=(R.portPart 0).edgeSet∪(R.portPart 1).edgeSet := by
    ext z;induction z using Sym2.inductionOn with | _ x y => rfl
  have all : G.edgeSet=R.erased.edgeSet∪R.adapted.edgeSet := by
    ext z;induction z using Sym2.inductionOn with
    | _ x y =>
      change G.Adj x y ↔ ((G.Adj x y ∧ ¬R.adapted.Adj x y) ∨ R.adapted.Adj x y)
      have sub : R.adapted.Adj x y → G.Adj x y := fun e => R.adapted_le e
      by_cases h : R.adapted.Adj x y
      · exact ⟨fun _ => Or.inr h,fun _ => sub h⟩
      · exact ⟨fun e => Or.inl ⟨e,h⟩,fun e => (e.resolve_right h).1⟩
  have apart : Disjoint R.erased.edgeSet R.adapted.edgeSet := by
    apply Set.disjoint_left.mpr;intro z
    induction z using Sym2.inductionOn with
    | _ x y => exact fun (e : R.erased.Adj x y) adj => e.2 adj
  have count := congrArg Set.ncard union
  rw [Set.ncard_union_eq R.portParts_disjoint_edges,R.portPart_edge_count 0,
    R.portPart_edge_count 1,R.box_edge_count cap 0,R.box_edge_count cap 1] at count
  have total := congrArg Set.ncard all
  rw [Set.ncard_union_eq apart] at total
  have c0 := charge 0
  have c1 := charge 1
  dsimp only [portCount,totalCapacity]
  omega

#print axioms portPart_edge_count
#print axioms portParts_disjoint_edges
#print axioms adapted_edge_account
end JSP452Audit.StarHost.NinePortRegion
