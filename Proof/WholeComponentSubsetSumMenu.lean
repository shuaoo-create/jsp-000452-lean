import StrictSixChosenEdgePrice
namespace JSP452Audit.StarHost
open SimpleGraph

def SplitCapacities {I:Type*} [Fintype I] [DecidableEq I] (z:I→ℕ) (r:ℕ) : Prop :=
  ∀i j,i+j=r+(∑k,z k) → ∃T:Finset I,(∑k∈T,z k) ≤ i ∧ (∑k∈Tᶜ,z k)≤j

theorem split_capacities_of_small {I:Type*} [Fintype I] [DecidableEq I] (z:I→ℕ) (r:ℕ) (small:∀k,z k≤r+1) :
    SplitCapacities z r := by
  intro i j sum
  obtain ⟨T,left,right,_⟩ := capacity_split z i j r sum small
  exact ⟨T,left,right⟩

theorem realized_capacity_menu_row {I X : Type*} [Fintype I] [DecidableEq I] [Finite X]
    (G Y : SimpleGraph X) (part : I → SimpleGraph X) (z : I → ℕ) {r s t : ℕ}
    (n m : ℕ → ℕ) (hn : Antitone n) (hm : Antitone m)
    (hY : Y≤G) (sub : ∀ k, part k≤G) (cover : G≤Y⊔(Finset.univ.sup part))
    (cost : ∀ T : Finset I, matchingEdges (T.sup part) ≤ ∑ k∈T,z k)
    (menu : SplitCapacities z r) (row : ForcingRow G s t n m r) :
    ForcingRow Y s t n m (r+∑ k,z k) := by
  classical
  intro i j l q ij il jq hl hq R incl
  obtain ⟨T,rx,by'⟩ := menu i j ij
  have total := Finset.sum_add_sum_compl T z
  let x := ∑ k∈T,z k
  let y := ∑ k∈Tᶜ,z k
  let i0 := i-x
  let j0 := j-y
  have xi : i0+x=i := Nat.sub_add_cancel rx
  have yj : j0+y=j := Nat.sub_add_cancel by'
  have totals : x+y = ∑ k,z k := total
  have old := row i0 j0 (x+l) (y+q) (by omega) (by omega) (by omega) (by omega) (by omega)
  have cover' : G≤(Y⊔T.sup part)⊔Tᶜ.sup part := by
    rw [sup_pieces_split part T,← sup_assoc] at cover
    exact cover
  rcases restored_pair_outcome G Y (T.sup part) (Tᶜ.sup part) hY
    (Finset.sup_le (fun k _ => sub k)) cover' _ _ old R incl with red | blue
  · exact Or.inl (xi ▸ trim_touched_forest R (T.sup part) n hn i0 x l (cost T) red)
  · exact Or.inr (yj ▸ trim_touched_forest (Y \ R) (Tᶜ.sup part) m hm j0 y q (cost _) blue)

theorem actual_piece_menu_of_splits {I X : Type*} [Fintype I] [DecidableEq I] [Finite X]
    (G : SimpleGraph X) (U : Set X) (part : I → SimpleGraph X) (z : I → ℕ) {r s t : ℕ}
    (n m : ℕ → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i<s, 0<n i) (pm : ∀ j<t, 0<m j)
    (sub : ∀ k, part k ≤ G) (cost : ∀ T : Finset I, matchingEdges (T.sup part) ≤ ∑ k∈T,z k)
    (menu : SplitCapacities z (r+U.ncard)) (row : ForcingRow G s t n m r) :
    ForcingRow ((G \ Finset.univ.sup part).induce Uᶜ) s t n m (r+U.ncard+∑ k,z k) := by
  let H := G.induce Uᶜ
  let Y := (G \ Finset.univ.sup part).induce Uᶜ
  let inner (k : I) := (part k).induce Uᶜ
  apply realized_capacity_menu_row H Y inner z n m hn hm
  · exact fun _ _ h => h.1
  · exact fun k _ _ h => sub k h
  · intro x y h
    by_cases edge : (Finset.univ.sup part).Adj x.val y.val
    · right
      change (Finset.univ.sup (fun k => (part k).induce Uᶜ)).Adj x y
      rw [induce_sup_pieces]
      exact edge
    · exact Or.inl ⟨h,edge⟩
  · intro T
    change matchingEdges (T.sup (fun k => (part k).induce Uᶜ)) ≤ _
    rw [induce_sup_pieces]
    exact (rank_mono_embedding (SimpleGraph.Embedding.induce (G := T.sup part) Uᶜ)).trans (cost T)
  · exact menu
  · exact row_delete_set G U n m hn hm pn pm row


#print axioms split_capacities_of_small
#print axioms realized_capacity_menu_row
#print axioms actual_piece_menu_of_splits
end JSP452Audit.StarHost
