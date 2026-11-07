import Mathlib.Combinatorics.SimpleGraph.Tutte

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} (H : SimpleGraph X) (v : X)


/-- The old component contains a neighbor of the restored vertex. -/
def componentTouches (c : (H.induce {x : X | x ≠ v}).ConnectedComponent) : Prop :=
  ∃ x ∈ c.supp, H.Adj x.val v

/-- Restore the original vertex labels in a component of the deleted graph. -/
def restoreComponent (c : (H.induce {x : X | x ≠ v}).ConnectedComponent) : H.ConnectedComponent :=
  c.map ({toFun := Subtype.val, map_rel' := fun h => h} : (H.induce {x : X | x ≠ v}) →g H)

@[simp] theorem restoreComponent_mk (x : {x : X // x ≠ v}) :
    restoreComponent H v ((H.induce {x : X | x ≠ v}).connectedComponentMk x) = H.connectedComponentMk x.val := rfl

theorem mem_restoreComponent {c : (H.induce {x : X | x ≠ v}).ConnectedComponent} {x : {x : X // x ≠ v}}
    (hx : x ∈ c.supp) : x.val ∈ (restoreComponent H v c).supp :=
  congrArg (restoreComponent H v) (show (H.induce {x : X | x ≠ v}).connectedComponentMk x = c from hx)

/-- The image of an untouched old component is edge-closed in the original graph,
so restoring v introduces no additional original vertex into its support. -/
theorem untouched_support_image (c : (H.induce {x : X | x ≠ v}).ConnectedComponent) (hc : ¬ componentTouches H v c) :
    Subtype.val '' c.supp = (restoreComponent H v c).supp := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x,hx,rfl⟩
    exact mem_restoreComponent H v hx
  · intro y hy
    obtain ⟨x,hx⟩ := c.nonempty_supp
    have reach := (restoreComponent H v c).reachable_of_mem_supp (mem_restoreComponent H v hx) hy
    rw [reachable_iff_reflTransGen] at reach
    clear hy
    induction reach with
    | refl => exact ⟨x,hx,rfl⟩
    | @tail a b _ edge ih =>
      obtain ⟨z,hz,heq⟩ := ih
      have hb : b ≠ v := by
        rintro rfl
        exact hc ⟨z,hz,heq.symm ▸ edge⟩
      have oldedge : (H.induce {x : X | x ≠ v}).Adj z ⟨b,hb⟩ := by change H.Adj z.val b; rwa [heq]
      exact ⟨⟨b,hb⟩,c.mem_supp_of_adj_mem_supp hz oldedge,rfl⟩

theorem componentTouches_iff_mem (c : (H.induce {x : X | x ≠ v}).ConnectedComponent) :
    componentTouches H v c ↔ v ∈ (restoreComponent H v c).supp := by
  constructor
  · rintro ⟨x,hx,edge⟩
    exact (restoreComponent H v c).mem_supp_of_adj_mem_supp (mem_restoreComponent H v hx) edge
  · intro hv
    by_contra hn
    rw [← untouched_support_image H v c hn] at hv
    obtain ⟨x,_,hx⟩ := hv
    exact x.property hx

theorem untouched_support_ncard (c : (H.induce {x : X | x ≠ v}).ConnectedComponent) (hc : ¬ componentTouches H v c) :
    c.supp.ncard = (restoreComponent H v c).supp.ncard := by
  rw [← untouched_support_image H v c hc]
  exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm

/-- The inverse is determined by the surviving labels of each component away from v. -/
noncomputable def untouchedComponentsEquiv :
    {c : (H.induce {x : X | x ≠ v}).ConnectedComponent // ¬ componentTouches H v c} ≃
    {d : H.ConnectedComponent // v ∉ d.supp} := by
  let f (c : {c : (H.induce {x : X | x ≠ v}).ConnectedComponent // ¬ componentTouches H v c}) :
      {d : H.ConnectedComponent // v ∉ d.supp} :=
    ⟨restoreComponent H v c.val,fun h => c.property ((componentTouches_iff_mem H v c.val).2 h)⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro c d eq
    obtain ⟨x,hx⟩ := c.val.nonempty_supp
    have hd : x.val ∈ (restoreComponent H v d.val).supp := by
      rw [← (show restoreComponent H v c.val = restoreComponent H v d.val from congrArg Subtype.val eq)]
      exact mem_restoreComponent H v hx
    rw [← untouched_support_image H v d.val d.property] at hd
    obtain ⟨z,hz,heq⟩ := hd
    have hx' : x ∈ d.val.supp := (Subtype.ext heq : z = x) ▸ hz
    exact Subtype.ext (ConnectedComponent.eq_of_common_vertex hx hx')
  · intro d
    obtain ⟨x,hx⟩ := d.val.nonempty_supp
    have hxv : x ≠ v := fun h => d.property (h ▸ hx)
    let c := (H.induce {x : X | x ≠ v}).connectedComponentMk ⟨x,hxv⟩
    have eq : restoreComponent H v c = d.val := hx
    have hc : ¬ componentTouches H v c := by
      intro hc
      exact d.property (eq ▸ (componentTouches_iff_mem H v c).1 hc)
    exact ⟨⟨c,hc⟩,Subtype.ext eq⟩

@[simp] theorem untouchedComponentsEquiv_apply
    (c : {c : (H.induce {x : X | x ≠ v}).ConnectedComponent // ¬ componentTouches H v c}) :
    (untouchedComponentsEquiv H v c).val = restoreComponent H v c.val := rfl


/-- Restoring v preserves exactly the count of all odd components outside its own. -/
theorem untouched_odd_count :
    ({c : (H.induce {x : X | x ≠ v}).ConnectedComponent |
      ¬ componentTouches H v c ∧ Odd c.supp.ncard} : Set _).ncard =
    ({d : H.ConnectedComponent | v ∉ d.supp ∧ Odd d.supp.ncard} : Set _).ncard := by
  let old := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun c => ¬ componentTouches H v c) (fun c => Odd c.supp.ncard)
  let new := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun d : H.ConnectedComponent => v ∉ d.supp) (fun d => Odd d.supp.ncard)
  let odd := Equiv.subtypeEquiv (untouchedComponentsEquiv H v)
    (p := fun c => Odd c.val.supp.ncard) (q := fun d => Odd d.val.supp.ncard)
    (fun c => by rw [untouchedComponentsEquiv_apply,untouched_support_ncard H v c.val c.property])
  exact Nat.card_congr ((old.symm.trans odd).trans new)

#print axioms untouched_odd_count

#print axioms untouched_support_image
#print axioms untouched_support_ncard
#print axioms untouchedComponentsEquiv
end JSP452Audit.StarHost
