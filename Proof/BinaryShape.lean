import BinaryRowProfile

namespace JSP452Audit.StarHost

/-- Count actual entries equal to two in the given source list. -/
def twoLeafCount {s : ℕ} (n : Fin s → ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin s)).filter (fun i => n i = 2)).card

theorem twoLeafCount_add_tail {s : ℕ} (n : Fin s → ℕ) :
    twoLeafCount n + (s - twoLeafCount n) = s := by
  have le := Finset.card_filter_le (s := (Finset.univ : Finset (Fin s))) (fun i => n i = 2)
  change ((Finset.univ : Finset (Fin s)).filter _).card + _ = _
  have count : twoLeafCount n ≤ s := by simpa [twoLeafCount] using le
  exact Nat.add_sub_of_le count

theorem twoLeafCount_pos_iff {s : ℕ} (n : Fin s → ℕ) : 0 < twoLeafCount n ↔ ∃ i, n i = 2 := by
  simp [twoLeafCount,Finset.card_pos,Finset.Nonempty]

/-- The two-leaf entries in a positive antitone list bounded by two form
exactly the initial segment of this length. -/
theorem binary_shape_at {s : ℕ} (n : Fin s → ℕ) (hn : Antitone n)
    (pos : ∀ i, 1 ≤ n i) (bound : ∀ i, n i ≤ 2) (i : Fin s) :
    n i = if i.val < twoLeafCount n then 2 else 1 := by
  let F := ((Finset.univ : Finset (Fin s)).filter (fun k => n k = 2))
  have inF (k : Fin s) : k ∈ F ↔ n k = 2 := by simp [F]
  by_cases head : n i = 2
  · let embed (k : Fin (i.val+1)) : Fin s := ⟨k.val,by have := k.isLt; have := i.isLt; omega⟩
    have above (k : Fin (i.val+1)) : n (embed k) = 2 := by
      have le : embed k ≤ i := by change k.val ≤ i.val; have := k.isLt; omega
      have := hn le
      have := bound (embed k)
      omega
    let into (k : Fin (i.val+1)) : ↥F := ⟨embed k,(inF _).mpr (above k)⟩
    have inj : Function.Injective into := fun _ _ eq => Fin.ext (congrArg (fun x : ↥F => x.val.val) eq)
    have enough : i.val+1 ≤ twoLeafCount n := by
      change i.val+1 ≤ F.card
      simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective into inj
    rw [if_pos (by omega)]; exact head
  · have before (j : ↥F) : j.val.val < i.val := by
      by_contra! no
      have le : i ≤ j.val := no
      have a := hn le
      have b := (inF _).mp j.property
      have d := bound i
      omega
    let into (j : ↥F) : Fin i.val := ⟨j.val.val,before j⟩
    have inj : Function.Injective into := fun _ _ eq => Subtype.ext (Fin.ext (congrArg (fun z : Fin i.val => z.val) eq))
    have short : twoLeafCount n ≤ i.val := by
      change F.card ≤ i.val
      simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective into inj
    rw [if_neg (by omega)]
    have := pos i
    have := bound i
    omega

/-- Relabel the source by the concrete binary profile without changing
any index value. Both lengths and the positive-two criterion are recorded. -/
theorem binary_shape {s : ℕ} (n : Fin s → ℕ) (hn : Antitone n)
    (pos : ∀ i, 1 ≤ n i) (bound : ∀ i, n i ≤ 2) :
    ∃ p a : ℕ, ∃ eq : s = p+a, p = twoLeafCount n ∧ a = s-p ∧
      (∀ i : Fin s, n i = binaryProfile p a (Fin.cast eq i)) ∧
      (0 < p ↔ ∃ i, n i = 2) := by
  let p := twoLeafCount n
  let a := s-p
  have eq : s = p+a := (twoLeafCount_add_tail n).symm
  exact ⟨p,a,eq,rfl,rfl,fun i => binary_shape_at n hn pos bound i,twoLeafCount_pos_iff n⟩

#print axioms twoLeafCount_add_tail
#print axioms binary_shape_at
#print axioms binary_shape
end JSP452Audit.StarHost
