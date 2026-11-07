import CubicPaidPathGroups
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Fintype X]

def cubicWhiteSite (G:SimpleGraph X) (U:Set X) (c:(G.induce U).ConnectedComponent) : Set X :=
  Subtype.val '' c.supp

theorem site_in_white (G:SimpleGraph X) (U:Set X) (c:(G.induce U).ConnectedComponent) :
    cubicWhiteSite G U c⊆U := by rintro _ ⟨v,_,rfl⟩;exact v.property

theorem site_closed_adj (G:SimpleGraph X) (U:Set X) (c:(G.induce U).ConnectedComponent)
    {x y:X} (hx:x∈cubicWhiteSite G U c) (hy:y∈U) (e:G.Adj x y) : y∈cubicWhiteSite G U c := by
  obtain ⟨u,cu,rfl⟩ := hx
  exact ⟨⟨y,hy⟩,(c.mem_supp_congr_adj (show (G.induce U).Adj u ⟨y,hy⟩ from e)).1 cu,rfl⟩

theorem site_cross_zero (G:SimpleGraph X) (U:Set X) (c:(G.induce U).ConnectedComponent) :
    crossCount G (cubicWhiteSite G U c) (U\cubicWhiteSite G U c)=0 :=
  crossCount_of_no_edges G _ _ (fun _ hx _ hy e => hy.2 (site_closed_adj G U c hx hy.1 e))

theorem sites_disjoint (G:SimpleGraph X) (U:Set X) (c d:(G.induce U).ConnectedComponent) (ne:c≠d) :
    Disjoint (cubicWhiteSite G U c) (cubicWhiteSite G U d) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨u,hu,rfl⟩ ⟨w,hw,eq⟩
  have same : w=u := Subtype.ext eq
  subst w
  exact ne ((show (G.induce U).connectedComponentMk u=c from hu).symm.trans hw)

theorem site_neighbor_bound (G:SimpleGraph X) (U:Set X) (c:(G.induce U).ConnectedComponent) (v:U)
    (hc:v∈c.supp) : fourWhiteDegree G U v.val+1≤Nat.card c.supp := by
  let N := G.neighborSet v.val∩U
  have sub : insert v.val N⊆cubicWhiteSite G U c := by
    rintro _ (rfl|h)
    · exact ⟨v,hc,rfl⟩
    · exact site_closed_adj G U c ⟨v,hc,rfl⟩ h.2 h.1
  have count := Set.ncard_le_ncard sub
  rw [Set.ncard_insert_of_notMem (fun h => G.irrefl h.1)] at count
  have size : (cubicWhiteSite G U c).ncard=Nat.card c.supp :=
    (Set.ncard_image_of_injective _ Subtype.val_injective).trans (Nat.card_coe_set_eq _).symm
  rw [size] at count;exact count

/-- Transport the indexed component isomorphism back to the original
vertex labels, preserving both directions of adjacency within the component. -/
theorem component_path_labels {n:ℕ} (G:SimpleGraph X) (U:Set X) (c:(G.induce U).ConnectedComponent)
    (Q:SimpleGraph (Fin n)) (e:Q ≃g c.toSimpleGraph) :
    ∃v:Fin n ↪ X,Set.range v=cubicWhiteSite G U c ∧ ∀i j,Q.Adj i j ↔ G.Adj (v i) (v j) := by
  let v : Fin n ↪ X := ⟨fun i => (e i).val.val,fun _ _ eq => e.injective (Subtype.ext (Subtype.ext eq))⟩
  refine ⟨v,?_,fun i j => ?_⟩
  · ext x
    constructor
    · rintro ⟨i,rfl⟩;exact ⟨(e i).val,(e i).property,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      obtain ⟨i,hit⟩ := e.surjective (⟨u,hu⟩:c.supp)
      exact ⟨i,congrArg (fun a:c.supp => a.val.val) hit⟩
  · exact e.map_rel_iff.symm

#print axioms site_closed_adj
#print axioms site_neighbor_bound
#print axioms component_path_labels
end JSP452Audit.StarHost
