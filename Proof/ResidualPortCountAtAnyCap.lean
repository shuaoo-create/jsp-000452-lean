import ExposureLabelsAtAnyPositiveCap
namespace JSP452Audit.StarHost.ExposureLabels
open SimpleGraph
variable {X:Type*} [Finite X] {G:SimpleGraph X} {D:ℕ} (L:ExposureLabels G D)

def base := G \ (L.M.spanningCoe⊔L.selected Set.univ)

theorem edge_parts_disjoint (A:Set ↥L.W) (v:X) :
    Disjoint (L.M.spanningCoe.neighborSet v) ((L.selected A).neighborSet v) := by
  apply Set.disjoint_left.mpr
  rintro y matched (⟨u,_,uv,_⟩|⟨u,_,uy,_⟩)
  · exact u.property.1 (uv ▸ L.M.edge_vert matched)
  · exact u.property.1 (uy ▸ L.M.edge_vert (show L.M.Adj y v from (show L.M.Adj v y from matched).symm))

theorem residual_degree_account (v:X) :
    (L.base.neighborSet v).ncard+(L.M.spanningCoe.neighborSet v).ncard+
      ((L.selected Set.univ).neighborSet v).ncard=(G.neighborSet v).ncard := by
  let D := L.M.spanningCoe⊔L.selected Set.univ
  have sub : D≤G := sup_le L.M.spanningCoe_le (L.selected_sub _)
  have parts : D.neighborSet v=L.M.spanningCoe.neighborSet v∪(L.selected Set.univ).neighborSet v := rfl
  have dis : Disjoint (L.base.neighborSet v) (D.neighborSet v) := Set.disjoint_left.mpr (fun _ h hit => h.2 hit)
  have all : L.base.neighborSet v∪D.neighborSet v=G.neighborSet v := by
    ext y
    constructor
    · rintro (h|h)
      · exact h.1
      · exact sub h
    · intro edge
      by_cases used:D.Adj v y
      · exact Or.inr used
      · exact Or.inl ⟨edge,used⟩
  have total := Set.ncard_union_eq dis
  rw [all,parts,Set.ncard_union_eq (L.edge_parts_disjoint _ v)] at total
  omega

theorem fiber_empty_off_matching (A:Set ↥L.W) {v:X} (away:v∉L.M.verts) : L.fiber A v=∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro u mem
  exact away (mem.2 ▸ L.tip_matched u)

theorem residual_degree_with_ports (cap:∀v,Nat.card (G.neighborSet v)≤D) (v:X) :
    (L.base.neighborSet v).ncard+(L.fiber Set.univ v).ncard≤D-1 := by
  have account := L.residual_degree_account v
  have total : (G.neighborSet v).ncard≤D := cap v
  by_cases covered : v∈L.M.verts
  · rw [L.selected_at_matched _ covered,Set.ncard_image_of_injective _ Subtype.val_injective] at account
    obtain ⟨w,matched,_⟩ := L.matching covered
    have positive : 0<(L.M.spanningCoe.neighborSet v).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨w,matched⟩
    omega
  · rw [L.fiber_empty_off_matching _ covered,Set.ncard_empty,Nat.add_zero]
    by_cases high : Nat.card (G.neighborSet v)=D
    · let u:↥L.W := ⟨v,covered,high⟩
      have edge : (L.selected Set.univ).Adj v (L.tip u) := Or.inl ⟨u,Set.mem_univ _,rfl,rfl⟩
      have positive : 0<((L.selected Set.univ).neighborSet v).ncard :=
        (Set.ncard_pos (Set.toFinite _)).mpr ⟨L.tip u,edge⟩
      omega
    · have lt : (G.neighborSet v).ncard<D := lt_of_le_of_ne total high
      omega

#print axioms edge_parts_disjoint
#print axioms residual_degree_account
#print axioms fiber_empty_off_matching
#print axioms residual_degree_with_ports
end JSP452Audit.StarHost.ExposureLabels
