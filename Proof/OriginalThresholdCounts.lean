import PrefixColumnTax
import ColumnUniformHost
namespace JSP452Audit.StarHost

/-- Number of entries of an original positive list meeting the threshold. -/
def originalThresholdCount {s : ℕ} (n : Fin s→ℕ) (a : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin s)).filter (fun i => a≤n i)).card

theorem original_threshold_prefix {s : ℕ} (n : Fin s→ℕ) (hn : Antitone n)
    (a : ℕ) (i : Fin s) : a≤n i ↔ i.val<originalThresholdCount n a := by
  classical
  let S := (Finset.univ : Finset (Fin s)).filter (fun j => a≤n j)
  constructor
  · intro hi
    let idx (j:Fin (i.val+1)) : Fin s := ⟨j.val,by have := j.isLt;have := i.isLt;omega⟩
    let f (j:Fin (i.val+1)) : ↥S := ⟨idx j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hi.trans (hn (show idx j ≤ i from Nat.le_of_lt_succ j.isLt))⟩⟩
    have bound := Fintype.card_le_of_injective f (fun x y eq => Fin.ext
      (congrArg (fun z:↥S => z.val.val) eq))
    simp only [Fintype.card_fin,Fintype.card_coe] at bound
    exact bound
  · contrapose!
    intro no
    let f (j:↥S) : Fin i.val := ⟨j.val.val,by
      by_contra! larger
      have up := hn (show i ≤ j.val from larger)
      have mem := (Finset.mem_filter.mp j.property).2
      omega⟩
    have bound := Fintype.card_le_of_injective f (fun x y eq => Subtype.ext (Fin.ext (congrArg (fun z : Fin i.val => z.val) eq)))
    change S.card ≤ i.val
    simpa only [Fintype.card_fin,Fintype.card_coe] using bound

theorem original_threshold_le_length {s : ℕ} (n : Fin s→ℕ) (a : ℕ) : originalThresholdCount n a≤s := by
  have sub := Finset.filter_subset (fun i => a≤n i) Finset.univ
  simpa [originalThresholdCount] using Finset.card_le_card sub

theorem original_threshold_one {s : ℕ} (n : Fin s→ℕ) (pn : ∀i,1≤n i) : originalThresholdCount n 1=s := by
  unfold originalThresholdCount
  rw [Finset.filter_true_of_mem (fun i _ => pn i),Finset.card_univ,Fintype.card_fin]

#print axioms original_threshold_prefix
#print axioms original_threshold_le_length
#print axioms original_threshold_one
end JSP452Audit.StarHost
