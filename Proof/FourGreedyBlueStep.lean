import FourGreedyWhiteStep
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Fintype X]

/-- If every white candidate hits fewer vertices, a largest covered
candidate loses its own blue bonus and pays the same 26 potential units. -/
theorem four_greedy_blue_gain (G : SimpleGraph X) (reg : ∀x,Nat.card (G.neighborSet x)=4)
    (U:Set X) (nonempty : U.Nonempty) (v:X) (blue : v∉U) (H : ℕ) (size : (fourHit G U v).ncard=H)
    (better : ∀x∈U,(fourHit G U x).ncard<H) :
    fourPotential G (U\fourHit G U v)+26≤fourPotential G U := by
  classical
  let A := fourHit G U v
  let R := U\A
  have count : A.ncard=H := size
  obtain ⟨sep,whole⟩ := four_hit_partition G U v
  have bound (x:X) (hx:x∈U) : fourWhiteDegree G U x+1<H := by
    have l := better x hx;rw [four_hit_card,if_pos hx] at l;exact l
  obtain ⟨x,hx⟩ := nonempty
  have small := bound x hx
  have two : 2≤H := by omega
  have total := four_complement_degree G U v (reg v)
  have dH : fourWhiteDegree G U v=H := by simpa only [four_hit_card,if_neg blue,Nat.add_zero] using size
  have hi : H≤4 := by omega
  let q := fourBlueWeight (H-2)
  let c := 10-q
  have qcap : q≤10 := by dsimp [q,fourBlueWeight];split_ifs <;> omega
  have fresh (w:X) (hw:w∈A) : fourBlueWeight (fourWhiteDegree G R w)+c≤10 := by
    have old := bound w hw.2
    have parts := four_degree_split G A R sep w
    rw [whole] at parts
    have after : fourWhiteDegree G R w≤H-2 := by omega
    have le : fourBlueWeight (fourWhiteDegree G R w)≤q := four_blue_small _ _ after
    dsimp [c];omega
  have old (w:X) (_ : w∈Uᶜ) : fourBlueWeight (fourWhiteDegree G R w)+
      (fourWhiteDegree G A w+(if v=w then 3 else 0))≤fourBlueWeight (fourWhiteDegree G U w) := by
    have parts := four_degree_split G A R sep w
    rw [whole] at parts
    by_cases eq:v=w
    · subst w
      have zero : fourWhiteDegree G R v=0 := four_center_after G U v
      have hit : fourWhiteDegree G A v=H := by omega
      rw [if_pos rfl,zero,hit,dH]
      simp [fourBlueWeight,show H≠0 by omega]
      omega
    rw [if_neg eq,Nat.add_zero,parts]
    exact four_blue_loss _ _
  have gain := four_potential_step G U A R sep whole _ _ fresh old
  rw [four_sum_const,count,four_sum_add,four_sum_single_label _ _ blue] at gain
  have cross := four_cross_lower G U A (6-H) (fun w hw => by
    have cap := bound w hw.2
    have deg := four_complement_degree G U w (reg w)
    omega)
  rw [count] at cross
  have payment : 26≤H*c+H*(6-H)+3 := by
    rcases (show H=2 ∨ H=3 ∨ H=4 by omega) with h|h|h <;> norm_num [c,q,fourBlueWeight,h]
  change fourPotential G R+26≤fourPotential G U
  omega

#print axioms four_greedy_blue_gain
end JSP452Audit.StarHost
