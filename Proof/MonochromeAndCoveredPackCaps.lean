import PhysicalPaletteRectangleTax
namespace JSP452Audit.StarHost
open SimpleGraph

theorem uniform_pack_rank_cap {X:Type*} [Finite X] (C:SimpleGraph X) (x:ℕ) (pos:0<x) :
    UniformPackCap C x (matchingEdges C) := by
  intro k copy
  simpa using forest_copy_matching C (fun _:Fin k => x) (fun _ => pos) copy

theorem uniform_pack_order_cap {X:Type*} [Finite X] (C:SimpleGraph X) (x:ℕ) (pos:0<x)
    (S:Set X) (supp:∀v w,C.Adj v w → v∈S) :
    UniformPackCap C x (S.ncard/(x+1)) := by
  intro k copy
  have bound := copy_threshold_supported_order C S supp (fun _:Fin k => x) x pos copy
  have tally : headTally (fun _:Fin k => x) x=k := by simp [headTally]
  rw [tally] at bound
  exact (Nat.le_div_iff_mul_le (by omega)).mpr bound

theorem uniform_pack_bot_cap {X:Type*} [Finite X] (x:ℕ) (pos:0<x) :
    UniformPackCap (⊥:SimpleGraph X) x 0 := by
  simpa only [matchingEdges_bot] using uniform_pack_rank_cap (⊥:SimpleGraph X) x pos

theorem mono_red_rectangle {X Y:Type*} [Finite X] [Finite Y] (O:SimpleGraph X) (C:SimpleGraph Y)
    {s t r x y a:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (rx:0<x) (byh:0<y)
    (cap:UniformPackCap C x a) (live:a<originalThresholdCount n x) (other:0<originalThresholdCount m y)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) :
    originalThresholdCount n x+originalThresholdCount m y-1-r≤uniformEnvelope O (x+y-1)+a := by
  have bound := palette_rectangle_tax O C C le_rfl n m hn hm rx byh cap
    (by rw [sdiff_self];exact uniform_pack_bot_cap y byh) live other row
  simpa only [Nat.add_zero] using bound

theorem mono_blue_rectangle {X Y:Type*} [Finite X] [Finite Y] (O:SimpleGraph X) (C:SimpleGraph Y)
    {s t r x y b:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (rx:0<x) (byh:0<y)
    (red:0<originalThresholdCount n x) (cap:UniformPackCap C y b) (live:b<originalThresholdCount m y)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) :
    originalThresholdCount n x+originalThresholdCount m y-1-r≤uniformEnvelope O (x+y-1)+b := by
  have bound := palette_rectangle_tax O C ⊥ bot_le n m hn hm rx byh (uniform_pack_bot_cap x rx)
    (by rw [sdiff_bot];exact cap) red live row
  simpa only [Nat.add_zero] using bound

theorem split_cover_palette {Y:Type*} [Finite Y] (C:SimpleGraph Y) (S:Set Y) (x y:ℕ) (rx:0<x) (byh:0<y) :
    ∃P:SimpleGraph Y,P≤C ∧ UniformPackCap P x (Sᶜ.ncard/(x+1)) ∧ UniformPackCap (C \ P) y S.ncard := by
  let P : SimpleGraph Y := {
    Adj v w := C.Adj v w ∧ v∉S ∧ w∉S
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
    loopless := ⟨fun v h => C.loopless.irrefl v h.1⟩ }
  have bound := matchingEdges_le_cover_card (C \ P) S (by
    intro v w e
    by_contra! h
    exact e.2 ⟨e.1,h.1,h.2⟩)
  exact ⟨P,(fun _ _ e => e.1),uniform_pack_order_cap P x rx Sᶜ (fun _ _ e => e.2.1),
    fun k copy => (uniform_pack_rank_cap _ y byh k copy).trans bound⟩

#print axioms uniform_pack_rank_cap
#print axioms uniform_pack_order_cap
#print axioms uniform_pack_bot_cap
#print axioms mono_red_rectangle
#print axioms mono_blue_rectangle
#print axioms split_cover_palette
end JSP452Audit.StarHost
