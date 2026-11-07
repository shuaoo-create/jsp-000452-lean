import DeletionBudget

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Pull back the actual pairs of a matching along an induced embedding. A
retained vertex whose only mate was lost is omitted from the matching vertices. -/
theorem admits_remainder_of_induced_embedding {X Y : Type*} [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (e : G ↪g H) {j : ℕ}
    (good : admits_matching_remainder H j) : admits_matching_remainder G j := by
  obtain ⟨M,hm,hcap⟩ := good
  let N : G.Subgraph := {
    verts := {x | ∃ y, M.Adj (e x) (e y)}
    Adj := fun x y => M.Adj (e x) (e y)
    adj_sub := fun edge => e.map_rel_iff.mp (M.adj_sub edge)
    edge_vert := fun edge => ⟨_,edge⟩
    symm := ⟨fun _ _ edge => edge.symm⟩ }
  have matching : N.IsMatching := by
    intro x hit
    obtain ⟨y,edge⟩ := hit
    exact ⟨y,edge,fun z other => e.injective (hm.eq_of_adj_left other edge)⟩
  refine ⟨N,matching,fun x => ?_⟩
  let incl (y : (G \ N.spanningCoe).neighborSet x) :
      (H \ M.spanningCoe).neighborSet (e x) :=
    ⟨e y.val,e.map_rel_iff.mpr y.property.1,y.property.2⟩
  have inj : Function.Injective incl := fun _ _ h =>
    Subtype.ext (e.injective (congrArg Subtype.val h))
  exact (Nat.card_le_card_of_injective incl inj).trans (hcap _)

/-- Removing a real vertex decreases the minimum deletion budget by zero or
one. Both inequalities transport full matching-and-remainder witnesses. -/
theorem deletionBudget_delete_vertex {X : Type*} [Finite X]
    (G : SimpleGraph X) (v : X) (j : ℕ) :
    deletionBudget (G.induce {x | x ≠ v}) j ≤ deletionBudget G j ∧
    deletionBudget G j ≤ deletionBudget (G.induce {x | x ≠ v}) j + 1 := by
  classical
  let H := G.induce {x | x ≠ v}
  constructor
  · obtain ⟨U,good,attains⟩ := deletionBudget_attained G j
    let W : Set {x : X // x ≠ v} := {x | x.val ∈ U}
    let e : H.induce Wᶜ ↪g G.induce Uᶜ := {
      toFun := fun x => ⟨x.val.val,x.property⟩
      inj' := fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun x : ↥(Uᶜ : Set X) => x.val) h))
      map_rel_iff' := Iff.rfl }
    have cost : W.ncard ≤ U.ncard :=
      Nat.card_le_card_of_injective (fun x : W => (⟨x.val.val,x.property⟩ : U))
        (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun x : U => x.val) h)))
    exact ((deletionBudget_le_of_witness H j W (admits_remainder_of_induced_embedding e good)).trans cost).trans_eq attains
  · obtain ⟨W,good,attains⟩ := deletionBudget_attained H j
    let image : Set X := Subtype.val '' W
    let U := insert v image
    have away (x : ↥(Uᶜ : Set X)) : x.val ≠ v :=
      fun eq => x.property (eq ▸ Set.mem_insert v image)
    let e : G.induce Uᶜ ↪g H.induce Wᶜ := {
      toFun := fun x => ⟨⟨x.val,away x⟩,fun hx => x.property (Set.mem_insert_of_mem _ ⟨_,hx,rfl⟩)⟩
      inj' := fun _ _ h => Subtype.ext (congrArg (fun y : ↥(Wᶜ : Set {x : X // x ≠ v}) => y.val.val) h)
      map_rel_iff' := Iff.rfl }
    have cost : image.ncard ≤ W.ncard := Set.ncard_image_le
    exact ((deletionBudget_le_of_witness G j U (admits_remainder_of_induced_embedding e good)).trans
      (Set.ncard_insert_le v image)).trans (Nat.add_le_add_right (cost.trans_eq attains) 1)

#print axioms admits_remainder_of_induced_embedding
#print axioms deletionBudget_delete_vertex
end JSP452Audit.StarHost
