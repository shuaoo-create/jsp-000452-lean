import RegionMenuSaving
import SelectedOutsideVertices
import SmallerSourcePrice
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
/-- Preserve the full positive surplus of this particular region through
an actual smaller forcing row, with at most p(p+1) weight loss. -/
theorem actual_weight_successor {X : Type u} [Finite X] (G : SimpleGraph X)
    (D : ℕ) (K : DegreeRegion G D) (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    {s t r : ℕ} (n m : ℕ → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i<s,0<n i) (pm : ∀j<t,0<m j) (row : ForcingRow G s t n m r)
    (heavy : ((D/2:ℕ):ℤ)*(((D/2:ℕ):ℤ)+1)<edgeSurplus (G.induce K.positiveCore) D) :
    ∃ (U : Set X) (T : Finset ↥K.positive),
      let Y := (G \ K.selectedGraph T).induce Uᶜ; let z := ∑ c∈T,K.pieceCapacity c
      let w := ∑ c∈T,K.pieceWeight c
      0 < U.ncard+z ∧ edgeSurplus (G.induce K.positiveCore) D-((D/2:ℕ):ℤ)*(((D/2:ℕ):ℤ)+1) ≤ w ∧
        ForcingRow Y s t n m (r+(U.ncard+z)) ∧
        (G.edgeSet.ncard:ℤ)=(Y.edgeSet.ncard:ℤ)+(D:ℤ)*(U.ncard+z:ℕ)+w := by
  classical
  let _ := Fintype.ofFinite ↥K.positive
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
  exact ⟨U,T,by omega,kept,by simpa only [Nat.add_assoc] using next,saving⟩

#print axioms actual_weight_successor
end JSP452Audit.StarHost
