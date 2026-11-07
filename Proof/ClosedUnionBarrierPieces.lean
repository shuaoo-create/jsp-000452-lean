import OddRegularExposureBounds
import CubicLowComponentLabel
namespace JSP452Audit.StarHost
open SimpleGraph

def insideBarrierPieces {X : Type*} (G : SimpleGraph X) (S U : Set X) :
    Set (G.induce Sᶜ).ConnectedComponent := {c | ∀z:c.supp, z.val.val∈U}

theorem inside_of_touching {X : Type*} [Finite X] (G : SimpleGraph X) (S U : Set X)
    (closed : ∀v∈U,∀w,G.Adj v w → w∈U) (c : (G.induce Sᶜ).ConnectedComponent)
    (z:c.supp) (zin:z.val.val∈U) : c∈insideBarrierPieces G S U := by
  let V : Set ↥(Sᶜ : Set X) := {v | v.val∈U}
  have all := cubic_closed_component (G.induce Sᶜ) V z.val zin
    (fun v hv w edge => closed v.val hv w.val edge)
  have label : (G.induce Sᶜ).connectedComponentMk z.val=c := z.property
  rw [label] at all
  exact fun w => all w.property

theorem augment_root_count {X : Type*} [Finite X] (G : SimpleGraph X) (S U : Set X)
    (closed : ∀v∈U,∀w,G.Adj v w → w∈U) (A : RootAllocation G S)
    (T : Set (G.induce Sᶜ).ConnectedComponent) :
    let W := T∪insideBarrierPieces G S U
    let N := rootNeighbors (rootIncidence G S)
    (N W \ N T).ncard≤(W \ T).ncard := by
  intro W N
  have newPlace (a:↥(N W \ N T)) : A.place a.val∈W \ T := by
    obtain ⟨c,mem,z,edge⟩ := a.property.1
    have inside : c∈insideBarrierPieces G S U := mem.resolve_left (fun old => a.property.2 ⟨c,old,z,edge⟩)
    have rootIn := closed z.val.val (inside z) a.val.val edge.symm
    obtain ⟨v,link⟩ := A.link a.val
    have member := inside_of_touching G S U closed (A.place a.val) v (closed _ rootIn _ link)
    exact ⟨Or.inr member,fun old => a.property.2 ⟨A.place a.val,old,v,link⟩⟩
  let index (a:↥(N W \ N T)) : ↥(W \ T) := ⟨A.place a.val,newPlace a⟩
  have inj : Function.Injective index := fun _ _ eq =>
    Subtype.ext (A.place.injective (congrArg Subtype.val eq))
  simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective index inj

#print axioms inside_of_touching
#print axioms augment_root_count
end JSP452Audit.StarHost
