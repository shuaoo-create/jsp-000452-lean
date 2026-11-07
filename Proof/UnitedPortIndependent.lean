import IndependentAugmentedLabels
import EvenGoodRegionSaving
import FreeBadPortIncidence

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Membership in the region of original labels tests the unique residual
component of the given label, regardless of which witness names it. -/
private theorem original_label_in_core {X : Type*} (G : SimpleGraph X) (S : Set X)
    (T : Set (G.induce Sᶜ).ConnectedComponent) (c : (G.induce Sᶜ).ConnectedComponent)
    (x : c.supp) : x.val.val ∈ regionCore G S T ↔ c∈T := by
  have owner : (G.induce Sᶜ).connectedComponentMk x.val=c := x.property
  constructor
  · rintro ⟨y,eq,inside⟩
    have same : y=x.val := Subtype.ext eq
    rwa [same,owner] at inside
  · intro inside; exact ⟨x.val,rfl,owner.symm ▸ inside⟩

/-- Combine the actual old labels and all selected good ports in a single
independent full-degree set. Every old point in the protected region is a
selected good port, and all old points lie outside the barrier roots. -/
theorem united_port_independent {X J : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (D : ℕ) (A : RootAllocation G S) (T : Set (G.induce Sᶜ).ConnectedComponent)
    (inside : T ⊆ goodFullClass G S D)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp)
    (cf : J ↪ (G.induce Sᶜ).ConnectedComponent) (r : J ↪ ↥S) (z : ∀ i, (cf i).supp)
    (bad : ∀ i, cf i∈badFree G S D A) (cap : ∀x, Nat.card (G.neighborSet x)≤D)
    (rootEdge : ∀ i, G.Adj (r i).val (pick (A.place (r i))).val.val)
    (freePick : ∀ c∈freeFull G S D A, c∈T →
      (pick c).val.val ∈ goodPortSet G S D T (largeGoodPieces G S D T) pick)
    (split : ∀ c∈largeGoodPieces G S D T, GoodPortSplit c.toSimpleGraph D)
    (baseIndependent : G.IsIndepSet (augmentedPortLabels G S D A pick cf r
      (fun i => pick (A.place (r i))) z))
    (baseFull : ∀ x∈augmentedPortLabels G S D A pick cf r (fun i => pick (A.place (r i))) z,
      Nat.card (G.neighborSet x)=D) :
    let I₀ := augmentedPortLabels G S D A pick cf r (fun i => pick (A.place (r i))) z
    let P := goodPortSet G S D T (largeGoodPieces G S D T) pick
    let I := I₀ ∪ P
    G.IsIndepSet I ∧ (∀ x∈I, Nat.card (G.neighborSet x)=D) ∧ P⊆I ∧
      I₀ ∩ regionCore G S T ⊆ P := by
  intro I₀ P I
  let B := largeGoodPieces G S D T
  let W := regionCore G S T
  have portsIndependent : G.IsIndepSet P := goodPortSet_independent G S D T B pick split
  have portsFull : ∀ x∈P, Nat.card (G.neighborSet x)=D :=
    goodPortSet_full G S D T B pick (fun _ hc => (inside hc).1)
  have region : P ⊆ W := by
    rintro _ ⟨c,x,hx,rfl⟩
    have member : x.val.val∈P := ⟨c,x,hx,rfl⟩
    exact (original_label_in_core G S T c x).mpr ((goodPortSet_member_iff G S D T B pick c x).mp member).1
  have outside : I₀ ⊆ Sᶜ := by
    rintro _ ((⟨c,_,rfl⟩|⟨i,rfl⟩)|⟨i,rfl⟩)
    · exact (pick c).val.property
    · exact (pick (A.place (r i))).val.property
    · exact (z i).val.property
  have captured : I₀ ∩ W ⊆ P := by
    rintro x ⟨old,member⟩
    rcases old with (⟨c,hc,rfl⟩|⟨i,rfl⟩)|⟨i,rfl⟩
    · exact freePick c hc ((original_label_in_core G S T c (pick c)).mp member)
    · exact goodPortSet_root_pick G S D T B pick _ ((original_label_in_core G S T _ _).mp member)
        (r i) (rootEdge i) (cap _)
    · have selected := (original_label_in_core G S T (cf i) (z i)).mp member
      exact ((bad i).2 (inside selected).2).elim
  have cross {x y : X} (old : x∈I₀) (port : y∈P) (adj : G.Adj x y) : False := by
    rcases regionCore_neighbor G S T (region port) adj.symm with root|sameRegion
    · obtain ⟨a,_,same⟩ := root
      exact outside old (same ▸ a.property)
    · exact portsIndependent (captured ⟨old,sameRegion⟩) port adj.ne adj
  refine ⟨?_,fun x hx => hx.elim (baseFull x) (portsFull x),Set.subset_union_right,captured⟩
  rintro x (hx|hx) y (hy|hy) ne adj
  · exact baseIndependent hx hy ne adj
  · exact cross hx hy adj
  · exact cross hy hx adj.symm
  · exact portsIndependent hx hy ne adj

#print axioms united_port_independent
end JSP452Audit.StarHost
