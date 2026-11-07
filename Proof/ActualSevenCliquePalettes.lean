import SmallPaletteForestOrders
namespace JSP452Audit.StarHost
open SimpleGraph

def sevenComplete : SimpleGraph (Fin 7) := ⊤
def sevenFive : SimpleGraph (Fin 7) :=
  fromRel (fun x y => x.val<5 ∧ y.val<5)
def sevenCycle : SimpleGraph (Fin 7) :=
  fromRel (fun x y => (x.val+1)%7=y.val)

private theorem card_neighbors_table (H:SimpleGraph (Fin 7)) (r:Fin 7→Fin 7→Prop) [DecidableRel r]
    (eq:∀x y,H.Adj x y ↔ r x y) (v:Fin 7) :
    Nat.card (H.neighborSet v)=(Finset.univ.filter (r v)).card := by
  classical
  have setEq : H.neighborSet v=(↑(Finset.univ.filter (r v)):Set (Fin 7)) := by
    ext x;simpa using eq v x
  rw [setEq]
  simp

theorem seven_cycle_caps :
    (∀v,Nat.card (sevenCycle.neighborSet v)≤2) ∧
    (∀v,Nat.card ((sevenComplete \ sevenCycle).neighborSet v)≤4) := by
  let near (v w:Fin 7) := v≠w ∧ ((v.val+1)%7=w.val ∨ (w.val+1)%7=v.val)
  let far (v w:Fin 7) := v≠w ∧ ¬(v≠w ∧ ((v.val+1)%7=w.val ∨ (w.val+1)%7=v.val))
  let dn : DecidableRel near := fun v w => inferInstanceAs (Decidable (v≠w ∧ ((v.val+1)%7=w.val ∨ (w.val+1)%7=v.val)))
  let df : DecidableRel far := fun v w => inferInstanceAs (Decidable (v≠w ∧ ¬(v≠w ∧ ((v.val+1)%7=w.val ∨ (w.val+1)%7=v.val))))
  have n : ∀v:Fin 7,(Finset.univ.filter (near v)).card≤2 := by decide +kernel
  have f : ∀v:Fin 7,(Finset.univ.filter (far v)).card≤4 := by decide +kernel
  exact ⟨fun v => (card_neighbors_table sevenCycle near (fun _ _ => Iff.rfl) v).trans_le (n v),
    fun v => (card_neighbors_table _ far (fun _ _ => Iff.rfl) v).trans_le (f v)⟩

theorem seven_five_support :
    ∃S:Set (Fin 7),S.ncard=5 ∧ (∀x y,sevenFive.Adj x y → x∈S) ∧
      ∀x y,(sevenComplete \ sevenFive).Adj x y → x∈Sᶜ ∨ y∈Sᶜ := by
  let A := Finset.univ.filter (fun x:Fin 7 => x.val<5)
  refine ⟨↑A,?_,?_,?_⟩
  · rw [Set.ncard_coe_finset];decide +kernel
  · intro x y edge
    apply Finset.mem_filter.mpr
    rcases edge.2 with h|h
    · exact ⟨Finset.mem_univ _,h.1⟩
    · exact ⟨Finset.mem_univ _,h.2⟩
  · intro x y edge
    by_contra! both
    have xx := (Finset.mem_filter.mp (show x∈A from Classical.not_not.mp both.1)).2
    have yy := (Finset.mem_filter.mp (show y∈A from Classical.not_not.mp both.2)).2
    exact edge.2 ⟨edge.1,Or.inl ⟨xx,yy⟩⟩

theorem seven_clique_edge_price : sevenComplete.edgeSet.ncard=21 := by
  change (⊤ : SimpleGraph (Fin 7)).edgeSet.ncard=21
  rw [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card]
  decide +kernel

#print axioms seven_cycle_caps
#print axioms seven_five_support
#print axioms seven_clique_edge_price
end JSP452Audit.StarHost
