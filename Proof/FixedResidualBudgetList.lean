import OriginalCubicEscapeExcluded
import Mathlib.Data.Finset.Sort
namespace JSP452Audit.StarHost

/-- Feasible sets of wholly internal original star labels. The same
finite family is used at every output corner and in every coloring. -/
structure RemovalBudget (s : ℕ) where
  choices : Finset (Finset (Fin s))
  present : choices.Nonempty

namespace RemovalBudget
variable {s : ℕ} (W : RemovalBudget s)

def loss : ℕ := W.choices.sup Finset.card
def len : ℕ := s-W.loss

theorem loss_le_order : W.loss≤s := by
  apply Finset.sup_le
  intro T _;simpa using T.card_le_univ

theorem removed_le_loss (T : ↥W.choices) : T.val.card ≤ W.loss :=
  Finset.le_sup T.property

theorem enough (T : ↥W.choices) : W.len≤T.valᶜ.card := by
  have cap := W.removed_le_loss T
  rw [Finset.card_compl,Fintype.card_fin];dsimp [len];omega

noncomputable def label (T : ↥W.choices) : Fin W.len ↪o Fin s :=
  T.valᶜ.orderEmbOfCardLe (W.enough T)

theorem label_kept (T : ↥W.choices) (i : Fin W.len) : W.label T i∉T.val :=
  Finset.mem_compl.mp (Finset.orderEmbOfCardLe_mem _ (W.enough T) i)

private theorem index_lower {l v : ℕ} (f : Fin l ↪o Fin v) (i : Fin l) : i.val≤(f i).val := by
  cases l with
  | zero => exact Fin.elim0 i
  | succ l =>
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have lt := f.strictMono (show k.castSucc < k.succ from Fin.castSucc_lt_succ)
      change (f k.castSucc).val<(f k.succ).val at lt
      change k.val+1≤(f k.succ).val
      change k.val≤(f k.castSucc).val at ih
      omega

theorem label_ge (T : ↥W.choices) (i : Fin W.len) : i.val≤(W.label T i).val :=
  index_lower (W.label T) i

/-- The minimum at each position ranges over entire feasible deletion
patterns. Its witness may vary by position, while the lower bound holds
on each individual surviving list simultaneously. -/
noncomputable def entries (n : Fin s→ℕ) (i : Fin W.len) : ℕ :=
  (W.choices.attach.image (fun T => n (W.label T i))).min'
    (by obtain ⟨T,h⟩ := W.present; exact ⟨_,Finset.mem_image.mpr ⟨⟨T,h⟩,Finset.mem_attach _ _,rfl⟩⟩)

theorem entries_le (n : Fin s→ℕ) (T : ↥W.choices) (i : Fin W.len) :
    W.entries n i≤n (W.label T i) := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨T,Finset.mem_attach _ _,rfl⟩)

theorem le_entries {n : Fin s→ℕ} {i : Fin W.len} {q : ℕ}
    (all : ∀T:↥W.choices,q≤n (W.label T i)) : q≤W.entries n i := by
  apply Finset.le_min'
  intro x hx
  obtain ⟨T,_,rfl⟩ := Finset.mem_image.mp hx;exact all T

theorem entries_antitone (n : Fin s→ℕ) (hn : Antitone n) : Antitone (W.entries n) := by
  intro i j ij
  apply W.le_entries
  intro T
  exact (W.entries_le n T j).trans (hn ((W.label T).monotone ij))

theorem entries_positive (n : Fin s→ℕ) (pn : ∀i,1≤n i) : ∀i, 1≤W.entries n i :=
  fun _ => W.le_entries (fun T => pn (W.label T _))

end RemovalBudget
#print axioms RemovalBudget.label_ge
#print axioms RemovalBudget.entries_le
#print axioms RemovalBudget.entries_antitone
#print axioms RemovalBudget.entries_positive
end JSP452Audit.StarHost
