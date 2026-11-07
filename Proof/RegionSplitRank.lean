import SumReserve
import LocalOddReplacement
import MaximalBarrier
import ParityGap
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
universe u v
theorem rank_mono_embedding {X : Type u} {Y : Type v} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (i : G ↪g H) : matchingEdges G ≤ matchingEdges H := by
  obtain ⟨M,hm,max⟩ := exists_maximum_matching G
  have plus := hm.map i.toHom i.injective
  have lim := le_matchingEdges plus
  have count := matching_vertices_eq_twice_edges plus
  have vals : (M.map i.toHom).verts = i '' M.verts := rfl
  rw [vals,Set.ncard_image_of_injective _ i.injective,matching_vertices_eq_twice_edges hm,max] at count
  omega

theorem rank_eq_of_graph_iso {X : Type u} {Y : Type v} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (i : G ≃g H) : matchingEdges G=matchingEdges H :=
  le_antisymm (rank_mono_embedding i.toEmbedding) (rank_mono_embedding i.symm.toEmbedding)

/-- The two projections retain the actual labels within a partition of an induced graph. -/
noncomputable def regionSumIso {X : Type u} (G : SimpleGraph X) (K P Q : Set X)
    (cover : P ∪ Q=K) (dis : Disjoint P Q) (sep : ∀ x∈P, ∀ y∈Q, ¬G.Adj x y) :
    (G.induce P ⊕g G.induce Q) ≃g G.induce K := by
  classical
  let join : ↥P ⊕ ↥Q → K := Sum.elim (fun x => ⟨x.val,cover ▸ Or.inl x.property⟩)
    (fun y => ⟨y.val,cover ▸ Or.inr y.property⟩)
  have inj : Function.Injective join := by
    rintro (a|a) (b|b) h
    · exact congrArg Sum.inl (Subtype.ext (congrArg (fun w : K => w.val) h))
    · have eq : a.val=b.val := congrArg (fun w : K => w.val) h
      exact False.elim ((Set.disjoint_left.mp dis) a.property (eq.symm ▸ b.property))
    · have eq : a.val=b.val := congrArg (fun w : K => w.val) h
      exact False.elim ((Set.disjoint_left.mp dis) b.property (eq ▸ a.property))
    · exact congrArg Sum.inr (Subtype.ext (congrArg (fun w : K => w.val) h))
  have onto (z : K) : ∃ w, join w=z := by
    have member : z.val ∈ P ∪ Q := cover.symm ▸ z.property
    rcases member with hp | hq
    · exact ⟨.inl ⟨z.val,hp⟩,rfl⟩
    · exact ⟨.inr ⟨z.val,hq⟩,rfl⟩
  refine ⟨Equiv.ofBijective join ⟨inj,onto⟩,?_⟩
  rintro (x|x) (y|y)
  · rfl
  · exact ⟨fun h => (sep x.val x.property y.val y.property h).elim, fun h => (not_adj_sum_inl_inr x y h).elim⟩
  · exact ⟨fun h => (sep y.val y.property x.val x.property ((show G.Adj x.val y.val from h).symm)).elim, fun h => (not_adj_sum_inl_inr y x h.symm).elim⟩
  · rfl

theorem rank_split_regions {X : Type u} [Finite X] (G : SimpleGraph X) (K P Q : Set X)
    (cover : P ∪ Q=K) (dis : Disjoint P Q) (sep : ∀ x∈P, ∀ y∈Q, ¬G.Adj x y) :
    matchingEdges (G.induce K)=matchingEdges (G.induce P)+matchingEdges (G.induce Q) := by
  rw [← rank_eq_of_graph_iso (regionSumIso G K P Q cover dis sep),matchingEdges_sumGraph]

/-- If no further cut gains over the empty cut, the same is true separately
on either part of any genuine disjoint union. -/
theorem unmatched_eq_odd_on_region {X : Type u} [Finite X] (G : SimpleGraph X) (K P Q : Set X)
    (cover : P ∪ Q=K) (dis : Disjoint P Q) (sep : ∀ x∈P, ∀ y∈Q, ¬G.Adj x y)
    (tight : minUnmatched (G.induce K) = (G.induce K).oddComponents.ncard) :
    minUnmatched (G.induce P) = (G.induce P).oddComponents.ncard := by
  have lb {Y : Type u} [Finite Y] (H : SimpleGraph Y) : H.oddComponents.ncard ≤ minUnmatched H := by
    have h := tutte_berge_upper_all H ∅
    rw [Set.compl_empty,Set.ncard_empty,Nat.zero_add,odd_ncard_iso (induceUnivIso H)] at h
    exact h
  have rp := lb (G.induce P)
  have rq := lb (G.induce Q)
  have iso := regionSumIso G K P Q cover dis sep
  have order := Nat.card_congr iso.toEquiv
  rw [Nat.card_sum] at order
  have rk := rank_split_regions G K P Q cover dis sep
  have odd := odd_ncard_iso iso
  rw [odd_ncard_sumGraph] at odd
  have k := minUnmatched_add_twice_matching (G.induce K)
  have p := minUnmatched_add_twice_matching (G.induce P)
  have q := minUnmatched_add_twice_matching (G.induce Q)
  omega
#print axioms rank_split_regions
#print axioms unmatched_eq_odd_on_region
end JSP452Audit.StarHost