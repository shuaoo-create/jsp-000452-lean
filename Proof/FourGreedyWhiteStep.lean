import FourGreedyNeighborhoodGain
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Fintype X]

/-- Choosing a white vertex with a largest closed white neighbourhood pays
26 potential units, including the degree-one-neighbourhood phase. -/
theorem four_greedy_white_gain (G : SimpleGraph X) (reg : ∀x,Nat.card (G.neighborSet x)=4)
    (U:Set X) (v:X) (white : v∈U) (H : ℕ) (size : (fourHit G U v).ncard=H)
    (largest : ∀x,(fourHit G U x).ncard≤H) :
    fourPotential G (U\fourHit G U v)+26≤fourPotential G U := by
  classical
  let A := fourHit G U v
  let R := U\A
  have vA : v∈A := ⟨Or.inl rfl,white⟩
  have count : A.ncard=H := size
  obtain ⟨sep,whole⟩ := four_hit_partition G U v
  have third (x:X) (hx:x∈U) : fourWhiteDegree G U x+1≤H := by
    have l := largest x;rw [four_hit_card,if_pos hx] at l;exact l
  have degree := four_complement_degree G U v (reg v)
  have self := four_hit_card G U v
  rw [if_pos white] at self
  have pos : 1≤H := by omega
  have hi : H≤5 := by omega
  let q := fourBlueWeight (H-2)
  let c := 10-q
  let b := if H=1 then 4 else 1
  have qcap : q≤10 := by dsimp [q,fourBlueWeight];split_ifs <;> omega
  have fresh (x:X) (hx:x∈A) :
      fourBlueWeight (fourWhiteDegree G R x)+(c+(if v=x then q else 0))≤10 := by
    by_cases eq:v=x
    · subst x
      have zero : fourWhiteDegree G R v=0 := four_center_after G U v
      rw [zero,if_pos rfl];dsimp [c,fourBlueWeight];omega
    rw [if_neg eq,Nat.add_zero]
    have hit : G.Adj v x := hx.1.resolve_left (Ne.symm eq)
    have one : 0<fourWhiteDegree G A x := (Set.ncard_pos (Set.toFinite _)).2 ⟨v,hit.symm,vA⟩
    have parts := four_degree_split G A R sep x
    rw [whole] at parts
    have old := third x hx.2
    have after : fourWhiteDegree G R x≤H-2 := by omega
    have le : fourBlueWeight (fourWhiteDegree G R x)≤q := four_blue_small _ _ after
    dsimp [c];omega
  have old (x:X) (hx:x∈Uᶜ) : fourBlueWeight (fourWhiteDegree G R x)+b*fourWhiteDegree G A x≤
      fourBlueWeight (fourWhiteDegree G U x) := by
    have max := largest x
    rw [four_hit_card,if_neg hx,Nat.add_zero] at max
    exact four_old_vertex_loss G A R U sep whole H x max
  have gain := four_potential_step G U A R sep whole _ _ fresh old
  have left : fourLabelSum A (fun x => c+(if v=x then q else 0))=H*c+q := by
    rw [four_sum_add,four_sum_const,four_sum_single_label _ _ vA,count]
  have right := four_sum_mul Uᶜ b (fourWhiteDegree G A)
  rw [left,right] at gain
  have cross := four_cross_lower G U A (5-H) (fun x hx => by
    have du := third x hx.2
    have tot := four_complement_degree G U x (reg x)
    omega)
  rw [count] at cross
  have charged := Nat.mul_le_mul_left b cross
  have payment : 26≤H*c+q+b*(H*(5-H)) := by
    rcases (show H=1 ∨ H=2 ∨ H=3 ∨ H=4 ∨ H=5 by omega) with h|h|h|h|h <;>
      norm_num [b,c,q,fourBlueWeight,h]
  change fourPotential G R+26≤fourPotential G U
  omega

#print axioms four_greedy_white_gain
end JSP452Audit.StarHost
