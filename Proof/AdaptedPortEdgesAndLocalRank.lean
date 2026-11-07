import OriginalEdgesOnPortLabels
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

/-- All edges incident with reserved vertices. This keeps exactly the internal
edges and, for an E block, its one port. -/
def portPart (i : Fin 2) : SimpleGraph X where
  Adj x y := G.Adj x y ∧ (x∈R.reserved i ∨ y∈R.reserved i)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem root_outside_box (i j : Fin 2) : (R.port i).root∉R.box j :=
  fun h => cut_piece_outside G R.K.barrier (R.select j).val.val h (Or.inl (R.port i).root_mem)

theorem internal_in_portPart (i : Fin 2) : portInside G (R.box i) ≤ R.portPart i := by
  classical
  intro x y edge
  obtain ⟨adj,hx,hy⟩ := (portInside_adj G (R.box i) x y).mp edge
  refine ⟨adj,?_⟩
  by_cases h : R.essential i
  · exact Or.inl (by rwa [reserved,if_pos h])
  · rw [reserved,if_neg h]
    by_cases xt : x=(R.port i).tip
    · exact Or.inr ⟨hy,fun yt => adj.ne (xt.trans ((Set.mem_singleton_iff.mp yt).symm))⟩
    · exact Or.inl ⟨hx,xt⟩

theorem tip_reserved_iff (i : Fin 2) : (R.port i).tip∈R.reserved i ↔ R.essential i := by
  classical
  by_cases h : R.essential i
  · rw [reserved,if_pos h]
    exact ⟨fun _ => h,fun _ => (R.port i).tip_mem⟩
  · rw [reserved,if_neg h]
    exact ⟨fun hx => (hx.2 (Set.mem_singleton _)).elim,fun he => (h he).elim⟩

theorem portPart_edges (i : Fin 2) (x y : X) : (R.portPart i).Adj x y ↔
    (portInside G (R.box i)).Adj x y ∨ (R.essential i ∧
      ((x=(R.port i).tip ∧ y=(R.port i).root) ∨ (y=(R.port i).tip ∧ x=(R.port i).root))) := by
  constructor
  · intro edge
    have orient (u v : X) (a : G.Adj u v) (hu : u∈R.reserved i) :
        (portInside G (R.box i)).Adj u v ∨
          (R.essential i ∧ u=(R.port i).tip ∧ v=(R.port i).root) := by
      have inside := R.reserved_subset i hu
      by_cases hv : v∈R.box i
      · exact Or.inl ((portInside_adj G (R.box i) u v).mpr ⟨a,inside,hv⟩)
      · have eq := (R.port i).only u inside v hv a
        exact Or.inr ⟨(R.tip_reserved_iff i).mp (eq.1 ▸ hu),eq⟩
    rcases edge.2 with left|right
    · rcases orient x y edge.1 left with h|⟨e,ends⟩
      · exact Or.inl h
      · exact Or.inr ⟨e,Or.inl ends⟩
    · rcases orient y x edge.1.symm right with h|⟨e,ends⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨e,Or.inr ends⟩
  · rintro (internal|⟨he,ends⟩)
    · exact R.internal_in_portPart i internal
    · rcases ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨(R.port i).edge,Or.inl ((R.tip_reserved_iff i).mpr he)⟩
      · exact ⟨(R.port i).edge.symm,Or.inr ((R.tip_reserved_iff i).mpr he)⟩

theorem portPart_rank (i : Fin 2) : matchingEdges (R.portPart i)=R.capacity i := by
  have lower := rank_le_of_copy (SimpleGraph.Copy.ofLE _ _ (R.internal_in_portPart i))
  rw [rank_of_internal_edges] at lower
  apply Nat.le_antisymm _ lower
  by_cases h : R.essential i
  · have lim := rank_paid_by_one_tip G (R.portPart i) (fun _ _ edge => edge.1)
      (R.tipDeleted i) (R.port i).tip (by
        intro x y edge hx hy
        rcases (R.portPart_edges i x y).mp edge with inside|⟨_,ends⟩
        · obtain ⟨_,xa,ya⟩ := (portInside_adj G (R.box i) x y).mp inside
          exact ⟨⟨xa,hx⟩,⟨ya,hy⟩⟩
        · exact (ends.elim (fun z => hx z.1) (fun z => hy z.1)).elim)
    exact lim.trans (Nat.le_of_lt_succ (by change R.tipRank i+1<R.capacity i+1;exact Nat.succ_lt_succ h))
  · have same : R.portPart i=portInside G (R.box i) := by
      ext x y
      exact ⟨fun e => ((R.portPart_edges i x y).mp e).resolve_right (fun z => h z.1),
        fun e => R.internal_in_portPart i e⟩
    rw [same,rank_of_internal_edges]

#print axioms root_outside_box
#print axioms internal_in_portPart
#print axioms tip_reserved_iff
#print axioms portPart_edges
#print axioms portPart_rank
end JSP452Audit.StarHost.NinePortRegion
