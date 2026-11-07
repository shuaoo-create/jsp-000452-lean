import FixedResidualBudgetList
namespace JSP452Audit.StarHost
open SimpleGraph

def originalSuffixLabel {s : ℕ} (i l : ℕ) (hl : i+l≤s) : Fin l ↪ Fin s where
  toFun z := ⟨i+z.val,by have := z.isLt;omega⟩
  inj' := fun _ _ eq => Fin.ext (Nat.add_left_cancel (congrArg Fin.val eq))

noncomputable def originalRemoved {s : ℕ} (i l : ℕ) (hl : i+l≤s) (U : Set (Fin l)) : Finset (Fin s) :=
  U.toFinite.toFinset.map (originalSuffixLabel i l hl)

/-- The admissibility condition is verified only on actual, wholly
internal, disjoint stars with their original suffix labels. -/
def AdmitsInternal {s : ℕ} {Y : Type*} (W : RemovalBudget s) (n : Fin s→ℕ) (H : SimpleGraph Y) : Prop :=
  ∀ (i l : ℕ) (hl : i+l≤s) (U : Set (Fin l)),
    (forest (fun z:U => n (originalSuffixLabel i l hl z.val))).IsContained H →
      originalRemoved i l hl U∈W.choices

/-- Read positions i through i+l-1 in the same surviving original
copy. Their bounds hold simultaneously for the fixed residual list. -/
theorem residual_in_surviving_suffix {X : Type*} {s : ℕ} (n : Fin s→ℕ) (W : RemovalBudget s)
    (R : SimpleGraph X) (i old l : ℕ) (length : i+old=s) (fits : i+l=W.len)
    (U : Set (Fin old)) (T : ↥W.choices) (eqT : T.val=originalRemoved i old length.le Uᶜ)
    (copy : (forest (fun z:U => n (originalSuffixLabel i old length.le z.val))).IsContained R) :
    (suffixStars (padDemand (W.entries n)) i l).IsContained R := by
  classical
  let p (k:Fin l) : Fin W.len := ⟨i+k.val,by have := k.isLt;omega⟩
  let x (k:Fin l) := W.label T (p k)
  have low (k:Fin l) : i≤(x k).val := by
    have h := W.label_ge T (p k);change i+k.val≤(x k).val at h;omega
  let w (k:Fin l) : Fin old := ⟨(x k).val-i,by have := (x k).isLt;have := low k;omega⟩
  have original (k:Fin l) : originalSuffixLabel i old length.le (w k)=x k := by
    apply Fin.ext
    change i+((x k).val-i)=(x k).val
    have := low k;omega
  have keep (k:Fin l) : w k∈U := by
    by_contra missing
    have inside : (w k) ∈ (Uᶜ : Set (Fin old)).toFinite.toFinset :=
      (Set.Finite.mem_toFinset _).mpr missing
    exact W.label_kept T (p k) (eqT ▸ Finset.mem_map.mpr ⟨w k,inside,original k⟩)
  let idx : Fin l ↪ U := {
    toFun := fun k => ⟨w k,keep k⟩
    inj' := by
                             intro a b eq
                             have wh : w a=w b := congrArg (fun z:U => z.val) eq
                             have same : x a=x b := (original a).symm.trans ((congrArg (originalSuffixLabel i old length.le) wh).trans (original b))
                             have pos := (W.label T).injective same
                             exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val pos)) }
  let small (k:Fin l) := padDemand (W.entries n) (i+k.val)
  let larger (z:U) := n (originalSuffixLabel i old length.le z.val)
  have fit (k:Fin l) : small k≤larger (idx k) := by
    have bound := W.entries_le n T (p k)
    change padDemand (W.entries n) (i+k.val)≤n (originalSuffixLabel i old length.le (w k))
    rw [original,padDemand,dif_pos (p k).isLt];exact bound
  exact (show (forest small).IsContained (forest larger) from ⟨subforestCopy small larger idx fit⟩).trans copy

#print axioms residual_in_surviving_suffix
end JSP452Audit.StarHost
