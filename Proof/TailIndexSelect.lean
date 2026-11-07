import Mathlib.Data.Finset.Sort

namespace JSP452Audit.StarHost

/-- An increasing embedding of l positions into x+l positions leaves
space for all subsequent indices. Consequently its a-th index is at most x+a. -/
theorem strict_index_offset_le {x l : ℕ} {f : Fin l → Fin (x+l)}
    (mono : StrictMono f) (a : Fin l) : (f a).val ≤ x + a.val := by
  cases l with
  | zero => exact Fin.elim0 a
  | succ l =>
    induction a using Fin.reverseInduction with
    | last =>
      have bound := (f (Fin.last l)).isLt
      change _ ≤ x+l
      omega
    | cast i ih =>
      have step : (f i.castSucc).val < (f i.succ).val := mono Fin.castSucc_lt_succ
      change (f i.succ).val ≤ x+(i.val+1) at ih
      change (f i.castSucc).val ≤ x+i.val
      omega

/-- Choose l original good labels in order, with the coordinate bound needed
to compare demand against the suffix of a nonincreasing list. -/
theorem select_good_tail_indices (x l : ℕ) (bad : Finset (Fin (x+l))) (budget : bad.card ≤ x) :
    ∃ labels : Fin l ↪ Fin (x+l), StrictMono labels ∧
      ∀ a, labels a ∉ bad ∧ (labels a).val ≤ x + a.val := by
  have enough : l ≤ badᶜ.card := by
    rw [Finset.card_compl,Fintype.card_fin]
    omega
  let select := badᶜ.orderEmbOfCardLe enough
  refine ⟨select.toEmbedding,select.strictMono,fun a => ?_⟩
  exact ⟨Finset.mem_compl.mp (Finset.orderEmbOfCardLe_mem _ enough a),
    strict_index_offset_le select.strictMono a⟩

#print axioms strict_index_offset_le
#print axioms select_good_tail_indices
end JSP452Audit.StarHost
