import EvenRegionLayerCost
import GoodSetSize
import ProtectedLayerSaving
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]
/-- Pay the entire good-region deficit at layer D-1 of the original
graph. The remainder of I may extend beyond this protected region. -/
theorem even_good_region_saving (G : SimpleGraph X) (S : Set X) (D : ℕ) (large : 2≤D)
    (even : Even D) (cap : ∀x,Nat.card (G.neighborSet x)≤D) (noReg : NoOriginalRegularCritical G D)
    (data : ∀c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion c.toSimpleGraph)
    (T : Set (G.induce Sᶜ).ConnectedComponent) (inside : T⊆goodFullClass G S D)
    (pick : ∀c : (G.induce Sᶜ).ConnectedComponent,c.supp) (h : ℕ)
    (balance : T.ncard=(rootNeighbors (rootIncidence G S) T).ncard+h)
    (I : Set X) (selected : goodPortSet G S D T (largeGoodPieces G S D T) pick ⊆ I) :
    h ≤ savedAt G I (D-1) := by
  let B := largeGoodPieces G S D T
  let P := goodPortSet G S D T B pick
  let R := regionRoots G S T
  let W := regionCore G S T
  have rootSize : R.ncard=(rootNeighbors (rootIncidence G S) T).ncard :=
    Set.ncard_image_of_injective _ Subtype.val_injective
  have split := large_good_piece_split G S D cap noReg (fun c => (data c).2) T inside
  have price := good_region_layer_cost G S D large even cap noReg data T inside
  have count := goodPortSet_size G S D T B pick (fun _ hc => hc.1) split h R.ncard (rootSize.symm ▸ balance)
  have belongs : P⊆W := by
    rintro x ⟨c,y,hy,rfl⟩
    have mem : y.val.val∈P := ⟨c,y,hy,rfl⟩
    have hc := ((goodPortSet_member_iff G S D T B pick c y).mp mem).1
    exact ⟨y.val,rfl,(show (G.induce Sᶜ).connectedComponentMk y.val=c from y.property).symm ▸ hc⟩
  have num := Set.ncard_le_ncard (show P⊆I∩W from fun _ hp => ⟨selected hp,belongs hp⟩)
  apply protected_layer_saving G I W R (D-1) h
  · intro x hx y edge outside
    exact (regionCore_neighbor G S T hx edge).resolve_right outside
  · change h+R.ncard+B.ncard≤P.ncard at count
    change deletionBudget (G.induce W) (D-1)≤B.ncard at price
    omega
#print axioms even_good_region_saving
end JSP452Audit.StarHost
