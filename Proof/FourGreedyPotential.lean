import FourActualDominatingSetPrice
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Fintype X]

/-- Sum over the original labels of a finite vertex set. -/
noncomputable def fourLabelSum (S : Set X) (f : X→ℕ) : ℕ := by classical exact ∑x∈S.toFinset,f x

theorem four_sum_mono (S : Set X) (f g : X→ℕ) (le : ∀x∈S,f x≤g x) :
    fourLabelSum S f≤fourLabelSum S g := by
  classical
  exact Finset.sum_le_sum (fun x h => le x (Set.mem_toFinset.mp h))

theorem four_sum_add (S : Set X) (f g : X→ℕ) :
    fourLabelSum S (fun v => f v+g v)=fourLabelSum S f+fourLabelSum S g := by
  classical
  exact Finset.sum_add_distrib

theorem four_sum_const (S : Set X) (c : ℕ) : fourLabelSum S (fun _ => c)=S.ncard*c := by
  classical
  simp [fourLabelSum,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]

theorem four_sum_mul (S : Set X) (k:ℕ) (f:X→ℕ) :
    fourLabelSum S (fun v => k*f v)=k*fourLabelSum S f := by
  classical
  exact (Finset.mul_sum _ _ _).symm

theorem four_sum_union (A B : Set X) (sep : Disjoint A B) (f : X→ℕ) :
    fourLabelSum (A∪B) f=fourLabelSum A f+fourLabelSum B f := by
  classical
  simp only [fourLabelSum,Set.toFinset_union]
  exact Finset.sum_union (Set.disjoint_toFinset.mpr sep)

theorem four_sum_single_label (S : Set X) (x:X) (mem : x∈S) (c:ℕ) [DecidableEq X] :
    fourLabelSum S (fun v => if x=v then c else 0)=c := by
  classical
  simp [fourLabelSum,mem]

noncomputable def fourWhiteDegree (G : SimpleGraph X) (U:Set X) (x:X) : ℕ :=
  (G.neighborSet x∩U).ncard

theorem four_degree_split (G : SimpleGraph X) (A B : Set X) (sep : Disjoint A B) (x:X) :
    fourWhiteDegree G (A∪B) x=fourWhiteDegree G A x+fourWhiteDegree G B x := by
  unfold fourWhiteDegree
  rw [Set.inter_union_distrib_left,Set.ncard_union_eq (sep.mono Set.inter_subset_right Set.inter_subset_right)]

theorem four_sum_cross (G : SimpleGraph X) (A B : Set X) :
    fourLabelSum A (fourWhiteDegree G B)=crossCount G A B := by
  classical
  rw [crossCount_eq_neighbor_sum]
  unfold fourLabelSum fourWhiteDegree
  exact Finset.sum_subtype _ (fun x => Set.mem_toFinset) _

/-- A covered vertex carries its number of neighbours in the remaining set,
with a bonus of three when it still has a neighbour there. -/
def fourBlueWeight (n:ℕ) : ℕ := if n=0 then 0 else 3+n

theorem four_blue_loss (l d : ℕ) : fourBlueWeight d+l≤fourBlueWeight (l+d) := by
  unfold fourBlueWeight;split_ifs <;> omega

theorem four_blue_small (n k:ℕ) (le:n≤k) : fourBlueWeight n≤fourBlueWeight k := by
  unfold fourBlueWeight;split_ifs <;> omega

noncomputable def fourPotential (G : SimpleGraph X) (U:Set X) : ℕ :=
  10*U.ncard+fourLabelSum Uᶜ (fun x => fourBlueWeight (fourWhiteDegree G U x))

/-- Remove the newly hit set A from the undominated labels. If each new
and old vertex has the displayed local gain, their sum is a global gain. -/
theorem four_potential_step (G : SimpleGraph X) (U A R : Set X)
    (sep : Disjoint A R) (whole : A∪R=U) (gW gC : X→ℕ)
    (fresh : ∀x∈A,fourBlueWeight (fourWhiteDegree G R x)+gW x≤10)
    (old : ∀x∈Uᶜ,fourBlueWeight (fourWhiteDegree G R x)+gC x≤fourBlueWeight (fourWhiteDegree G U x)) :
    fourPotential G R+fourLabelSum A gW+fourLabelSum Uᶜ gC≤fourPotential G U := by
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
  unfold fourPotential
  rw [split,four_sum_union _ _ uc,count]
  rw [Nat.mul_comm A.ncard 10] at w
  omega

#print axioms four_sum_cross
#print axioms four_blue_loss
#print axioms four_potential_step
end JSP452Audit.StarHost
