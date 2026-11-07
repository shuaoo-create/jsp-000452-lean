import RegionMenuSaving
import SelectedOutsideVertices
import SmallerSourcePrice
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
/-- The integer target includes rounding up the lower bound for the weight
of positive whole components. -/
noncomputable def selectorTarget {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ) : ℤ :=
  ((D:ℤ)*(minimumExposure G D:ℤ)+1)/2 - ((D/2:ℕ):ℤ)*(((D/2:ℕ):ℤ)+1)

theorem heavy_region_successor {X : Type u} [Finite X] (G : SimpleGraph X)
    (D : ℕ) (K : DegreeRegion G D) (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    {s t r : ℕ} (n m : ℕ → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i<s,0<n i) (pm : ∀j<t,0<m j) (row : ForcingRow G s t n m r)
    (positive : 0<selectorTarget G D) :
    ∃ (U : Set X) (T : Finset ↥K.positive),
      let Y := (G \ K.selectedGraph T).induce Uᶜ; let z := ∑ c∈T,K.pieceCapacity c
      let w := ∑ c∈T,K.pieceWeight c
      0 < U.ncard+z ∧ selectorTarget G D ≤ w ∧
        ForcingRow Y s t n m (r+(U.ncard+z)) ∧
        (G.edgeSet.ncard:ℤ)=(Y.edgeSet.ncard:ℤ)+(D:ℤ)*(U.ncard+z:ℕ)+w := by
  classical
  let _ := Fintype.ofFinite ↥K.positive
  have weight := K.weight_identity cap
  have dom := positivePieces_dominate G K.barrier K.pieces D
  change edgeSurplus (G.induce K.core) D ≤ edgeSurplus (G.induce K.positiveCore) D at dom
  have lower : ((D:ℤ)*(minimumExposure G D:ℤ)+1)/2 ≤ edgeSurplus (G.induce K.positiveCore) D := by omega
  have heavy : ((D/2:ℕ):ℤ)*(((D/2:ℕ):ℤ)+1) < edgeSurplus (G.induce K.positiveCore) D := by
    unfold selectorTarget at positive; omega
  obtain ⟨T,_,card,order,kept,nonzero,c,mem,largest⟩ := K.choose_heavy_pieces cap heavy
  let Z := K.pieceCapacity c
  let b := Z-(r+1)
  obtain ⟨U,size,indep,full,away⟩ := selected_outside_vertices K T Z b card (fun i h => order i h c mem)
    cap (by dsimp [b]; omega)
  have small (i) (hi : i∈T) : K.pieceCapacity i ≤ r+U.ncard+1 := by
    have le : K.pieceCapacity i ≤ Z := largest i hi
    rw [size]; dsimp [b]; omega
  have ⟨next,saving⟩ := K.selected_menu_saving T U n m hn hm pn pm indep full away small row
  have sum : K.pieceCapacity c ≤ ∑ a∈T,K.pieceCapacity a :=
    Finset.single_le_sum (fun a _ => Nat.zero_le (K.pieceCapacity a)) mem
  have cz := nonzero c mem
  exact ⟨U,T,by omega,by unfold selectorTarget; omega,by simpa only [Nat.add_assoc] using next,saving⟩

/-- Operational lower price on sources up to and including the first strict
rank, provided the proposed gain beats the tax of the actual height column. -/
theorem selector_positive_price {s t : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    {X : Type u} [Finite X] (G : SimpleGraph X) (r D N : ℕ)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (live : 0<rowCount s t r) (upper : rowCount s t r≤N)
    (paid : AllSmallerPaid.{u} N) (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    (height : diagonal n m (r+2)≤D+1)
    (gain : 0<selectorTarget G D) :
    (rowEnergy n m r:ℤ)+selectorTarget G D ≤ (G.edgeSet.ncard:ℤ)+(widthAt n m r (D+1):ℤ) := by
  obtain ⟨K⟩ := degreeRegion_exists G D
  obtain ⟨U,T,progress,heavy,next,saving⟩ := heavy_region_successor G D K cap _ _
    (pad_antitone n hn) (pad_antitone m hm) (pad_positive n pn) (pad_positive m pm) row gain
  have price := smaller_source_price hs ht n m hn hm pn pm G _ r _ D N paid live upper progress height next _ saving
  omega
#print axioms heavy_region_successor
#print axioms selector_positive_price
end JSP452Audit.StarHost