import SumReserve
import RegionSplitRank
import DeletionStep

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Pull a witnessed deletion back through an induced embedding. Its cardinal
cost cannot increase because the vertex map is injective. -/
theorem deletionBudget_mono_embedding {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {J : SimpleGraph Y} (e : G ↪g J) (j : ℕ) :
    deletionBudget G j ≤ deletionBudget J j := by
  obtain ⟨U,good,best⟩ := deletionBudget_attained J j
  let W : Set X := e ⁻¹' U
  let incl : G.induce Wᶜ ↪g J.induce Uᶜ := {
    toFun := fun x => ⟨e x.val,x.property⟩
    inj' := fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h))
    map_rel_iff' := e.map_rel_iff }
  have pull := admits_remainder_of_induced_embedding incl good
  let f (x : W) : U := ⟨e x.val,x.property⟩
  have inj : Function.Injective f := fun _ _ h =>
    Subtype.ext (e.injective (congrArg (fun z : U => z.val) h))
  have le : W.ncard ≤ U.ncard := Nat.card_le_card_of_injective f inj
  exact ((deletionBudget_le_of_witness G j W pull).trans le).trans_eq best

theorem deletionBudget_iso {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {J : SimpleGraph Y} (e : G ≃g J) (j : ℕ) :
    deletionBudget G j = deletionBudget J j :=
  le_antisymm (deletionBudget_mono_embedding e.toEmbedding j)
    (deletionBudget_mono_embedding e.symm.toEmbedding j)

theorem baseReserve_iso {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {J : SimpleGraph Y} (e : G ≃g J) (H : ℕ) :
    baseReserve G H = baseReserve J H := by
  have edges : G.edgeSet.ncard = J.edgeSet.ncard := Nat.card_congr e.mapEdgeSet
  have budgets : deletionBudget G = deletionBudget J := funext (deletionBudget_iso e)
  simp only [baseReserve,edges,rank_eq_of_graph_iso e,budgets]

/-- Split off one actual component and retain its exact reserve plus that
of the complementary induced graph. -/
theorem baseReserve_split_component {X : Type*} [Finite X] (G : SimpleGraph X) (H : ℕ)
    (c : G.ConnectedComponent) :
    baseReserve G H = baseReserve c.toSimpleGraph H + baseReserve (G.induce c.suppᶜ) H := by
  have sep : ∀ x ∈ c.supp, ∀ y ∈ c.suppᶜ, ¬G.Adj x y :=
    fun _ hx _ hy edge => hy (c.mem_supp_of_adj_mem_supp hx edge)
  let e := (regionSumIso G Set.univ c.supp c.suppᶜ (Set.union_compl_self c.supp)
    disjoint_compl_right sep).trans (induceUnivIso G)
  exact (baseReserve_iso e H).symm.trans (baseReserve_sumGraph _ _ H)

theorem baseReserve_component_le {X : Type*} [Finite X] (G : SimpleGraph X) (H : ℕ)
    (c : G.ConnectedComponent) : baseReserve c.toSimpleGraph H ≤ baseReserve G H := by
  have split := baseReserve_split_component G H c
  omega

theorem baseReserve_zero_components {X : Type*} [Finite X] (G : SimpleGraph X) (H : ℕ)
    (zero : baseReserve G H = 0) (c : G.ConnectedComponent) : baseReserve c.toSimpleGraph H = 0 :=
  Nat.eq_zero_of_le_zero ((baseReserve_component_le G H c).trans_eq zero)

#print axioms deletionBudget_mono_embedding
#print axioms deletionBudget_iso
#print axioms baseReserve_iso
#print axioms baseReserve_split_component
#print axioms baseReserve_zero_components
end JSP452Audit.StarHost
