import FourGreedyPotential
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Fintype X]

def fourHit (G : SimpleGraph X) (U:Set X) (v:X) : Set X := (insert v (G.neighborSet v))∩U

theorem four_hit_card (G : SimpleGraph X) (U:Set X) (v:X) [Decidable (v∈U)] :
    (fourHit G U v).ncard=fourWhiteDegree G U v+(if v∈U then 1 else 0) := by
  by_cases yes:v∈U
  · rw [if_pos yes]
    have eq : fourHit G U v=insert v (G.neighborSet v∩U) := by ext w; simp [fourHit];aesop
    rw [eq,Set.ncard_insert_of_notMem (fun h => G.irrefl h.1)]
    rfl
  · rw [if_neg yes,Nat.add_zero]
    have eq : fourHit G U v=G.neighborSet v∩U := by ext w;simp [fourHit];aesop
    rw [eq];rfl

theorem four_hit_partition (G : SimpleGraph X) (U:Set X) (v:X) :
    Disjoint (fourHit G U v) (U\fourHit G U v) ∧ fourHit G U v∪(U\fourHit G U v)=U := by
  refine ⟨Set.disjoint_sdiff_right,?_⟩
  rw [Set.union_comm]
  exact Set.sdiff_union_of_subset (show fourHit G U v⊆U from Set.inter_subset_right)

theorem four_center_after (G : SimpleGraph X) (U:Set X) (v:X) :
    fourWhiteDegree G (U\fourHit G U v) v=0 := by
  have eq : G.neighborSet v∩(U\fourHit G U v)=∅ := Set.eq_empty_iff_forall_notMem.mpr (fun w h =>
    h.2.2 ⟨Or.inr h.1,h.2.1⟩)
  unfold fourWhiteDegree;rw [eq,Set.ncard_empty]

theorem four_complement_degree (G : SimpleGraph X) (U:Set X) (v:X) (reg : Nat.card (G.neighborSet v)=4) :
    fourWhiteDegree G U v+fourWhiteDegree G Uᶜ v=4 := by
  have eq := four_degree_split G U Uᶜ disjoint_compl_right v
  rw [Set.union_compl_self] at eq
  have total : fourWhiteDegree G Set.univ v=4 := by
    unfold fourWhiteDegree;rw [Set.inter_univ,←Nat.card_coe_set_eq,reg]
  omega

theorem four_cross_lower (G : SimpleGraph X) (U A:Set X) (b:ℕ)
    (each : ∀x∈A,b≤fourWhiteDegree G Uᶜ x) :
    A.ncard*b≤fourLabelSum Uᶜ (fourWhiteDegree G A) := by
  have cnt := four_sum_mono A _ _ each
  rw [four_sum_const,four_sum_cross,crossCount_swap G A Uᶜ,←four_sum_cross] at cnt
  exact cnt

/-- The gain from an old covered vertex is at least its number of edges
into A. If at most one white label could be hit anywhere, each such edge
also exhausts the blue bonus of three. -/
theorem four_old_vertex_loss (G : SimpleGraph X) (A R U:Set X) (sep : Disjoint A R) (whole:A∪R=U)
    (H : ℕ) (x:X) (cap : fourWhiteDegree G U x≤H) :
    fourBlueWeight (fourWhiteDegree G R x)+(if H=1 then 4 else 1)*fourWhiteDegree G A x≤
      fourBlueWeight (fourWhiteDegree G U x) := by
  have parts := four_degree_split G A R sep x
  rw [whole] at parts
  rw [parts]
  by_cases one:H=1
  · rw [if_pos one]
    have small : fourWhiteDegree G A x+fourWhiteDegree G R x≤1 := by omega
    unfold fourBlueWeight;split_ifs <;> omega
  · rw [if_neg one,Nat.one_mul];exact four_blue_loss _ _

#print axioms four_hit_card
#print axioms four_cross_lower
#print axioms four_old_vertex_loss
end JSP452Audit.StarHost
