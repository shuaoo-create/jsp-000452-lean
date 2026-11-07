import CubicActualFifthsPrice
import FourGreedyNeighborhoodGain
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Fintype X]

def cubicBlueWeight (n:ℕ) : ℕ := if n=0 then 0 else if 3≤n then 2 else 1
noncomputable def cubicGroupPotential (G:SimpleGraph X) (U:Set X) : ℕ :=
  2*U.ncard+fourLabelSum Uᶜ (fun x => cubicBlueWeight (fourWhiteDegree G U x))

theorem cubic_blue_monotone {a b:ℕ} (le:a≤b) : cubicBlueWeight a≤cubicBlueWeight b := by
  unfold cubicBlueWeight;split_ifs <;> omega

theorem cubic_potential_step (G : SimpleGraph X) (U A R : Set X)
    (sep : Disjoint A R) (whole : A∪R=U) (gW gC : X→ℕ)
    (fresh : ∀x∈A,cubicBlueWeight (fourWhiteDegree G R x)+gW x≤2)
    (old : ∀x∈Uᶜ,cubicBlueWeight (fourWhiteDegree G R x)+gC x≤cubicBlueWeight (fourWhiteDegree G U x)) :
    cubicGroupPotential G R+fourLabelSum A gW+fourLabelSum Uᶜ gC≤cubicGroupPotential G U := by
  have split : Rᶜ=Uᶜ∪A := by
    ext x
    have dis := Set.disjoint_left.mp sep
    rw [←whole];simp only [Set.mem_compl_iff,Set.mem_union]
    by_cases ra : x∈A <;> by_cases rr : x∈R <;> simp_all
  have uc : Disjoint Uᶜ A := Set.disjoint_left.mpr (fun _ h a => h (whole ▸ Or.inl a))
  have c := four_sum_mono Uᶜ _ _ old
  rw [four_sum_add] at c
  have w := four_sum_mono A _ _ fresh
  rw [four_sum_add,four_sum_const] at w
  have count : U.ncard=A.ncard+R.ncard := by rw [←whole,Set.ncard_union_eq sep]
  unfold cubicGroupPotential
  rw [split,four_sum_union _ _ uc,count]
  rw [Nat.mul_comm A.ncard 2] at w
  omega

/-- A three-white-neighbour white centre or, after those disappear, a
three-white-neighbour blue centre pays five units. In the remaining state
every vertex sees at most two undominated neighbours. -/
theorem cubic_early_step (G : SimpleGraph X) (cap : ∀x,Nat.card (G.neighborSet x)≤3)
    (U:Set X) :
    (∀x,fourWhiteDegree G U x≤2) ∨ ∃v:X,0<(fourHit G U v).ncard ∧
      cubicGroupPotential G (U\fourHit G U v)+5≤cubicGroupPotential G U := by
  classical
  have bounded (x:X) : fourWhiteDegree G U x≤3 :=
    (Set.ncard_le_ncard Set.inter_subset_left).trans ((Nat.card_coe_set_eq _).symm.le.trans (cap x))
  by_cases white : ∃v∈U,3≤fourWhiteDegree G U v
  · obtain ⟨v,inside,large⟩ := white
    let A := fourHit G U v
    let R := U\A
    have vA : v∈A := ⟨Or.inl rfl,inside⟩
    obtain ⟨sep,whole⟩ := four_hit_partition G U v
    have num : A.ncard=4 := by
      change (fourHit G U v).ncard=4
      rw [four_hit_card,if_pos inside];have := bounded v;omega
    have fresh (x:X) (hx:x∈A) : cubicBlueWeight (fourWhiteDegree G R x)+(1+(if v=x then 1 else 0))≤2 := by
      by_cases eq:v=x
      · subst x
        have zero : fourWhiteDegree G R v=0 := four_center_after G U v
        simp [zero,cubicBlueWeight]
      have e : G.Adj v x := hx.1.resolve_left (Ne.symm eq)
      have part := four_degree_split G A R sep x
      rw [whole] at part
      have one : 0<fourWhiteDegree G A x := (Set.ncard_pos (Set.toFinite _)).2 ⟨v,e.symm,vA⟩
      have h := bounded x
      have two : fourWhiteDegree G R x≤2 := by omega
      rw [if_neg eq];unfold cubicBlueWeight;split_ifs <;> omega
    have old (x:X) (_ : x∈Uᶜ) : cubicBlueWeight (fourWhiteDegree G R x)+0≤cubicBlueWeight (fourWhiteDegree G U x) := by
      have part := four_degree_split G A R sep x
      rw [whole] at part
      exact cubic_blue_monotone (by omega)
    have paid := cubic_potential_step G U A R sep whole _ _ fresh old
    rw [four_sum_const,four_sum_add,four_sum_const,four_sum_single_label A v vA,num] at paid
    exact Or.inr ⟨v,by change 0<A.ncard;omega,by change cubicGroupPotential G R+5≤_;omega⟩
  by_cases residual : ∀x,fourWhiteDegree G U x≤2
  · exact Or.inl residual
  push Not at residual
  obtain ⟨v,high⟩ := residual
  have outside : v∉U := fun hv => white ⟨v,hv,high⟩
  let A := fourHit G U v
  let R := U\A
  obtain ⟨sep,whole⟩ := four_hit_partition G U v
  have num : A.ncard=3 := by
    change (fourHit G U v).ncard=3
    rw [four_hit_card,if_neg outside];have := bounded v;omega
  have fresh (x:X) (hx:x∈A) : cubicBlueWeight (fourWhiteDegree G R x)+1≤2 := by
    have low : fourWhiteDegree G U x≤2 := by
      by_contra! large;exact white ⟨x,hx.2,large⟩
    have part := four_degree_split G A R sep x
    rw [whole] at part
    unfold cubicBlueWeight;split_ifs <;> omega
  have old (x:X) (_ : x∈Uᶜ) : cubicBlueWeight (fourWhiteDegree G R x)+(if v=x then 2 else 0)≤
      cubicBlueWeight (fourWhiteDegree G U x) := by
    by_cases eq:v=x
    · subst x
      have zero : fourWhiteDegree G R v=0 := four_center_after G U v
      simp [zero,cubicBlueWeight,show fourWhiteDegree G U v≠0 by omega,show 3≤fourWhiteDegree G U v by omega]
    · rw [if_neg eq,Nat.add_zero]
      have part := four_degree_split G A R sep x
      rw [whole] at part;exact cubic_blue_monotone (by omega)
  have paid := cubic_potential_step G U A R sep whole _ _ fresh old
  rw [four_sum_const,four_sum_single_label Uᶜ v outside,num] at paid
  exact Or.inr ⟨v,by change 0<A.ncard;omega,by change cubicGroupPotential G R+5≤_;omega⟩

#print axioms cubic_potential_step
#print axioms cubic_early_step
end JSP452Audit.StarHost
