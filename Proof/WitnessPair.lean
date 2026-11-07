import FiniteDemand
import HostAntidiagonal

namespace JSP452Audit.StarHost
open SimpleGraph

abbrev oneStar (a : ℕ) := forest (fun _ : Fin 1 => a)

/-- A designated component is an actual subgraph copy, with all its leaves. -/
theorem oneStar_in_forest {I : Type*} (n : I → ℕ) (i : I) :
    (oneStar (n i)).IsContained (forest n) := by
  let f : Vertices (fun _ : Fin 1 => n i) → Vertices n := fun z => ⟨i,z.2⟩
  have inj : Function.Injective f := by
    rintro ⟨p,a⟩ ⟨q,b⟩ h
    obtain rfl : p=q := Subsingleton.elim _ _
    have e : a=b := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact congrArg (Sigma.mk p) e
  refine ⟨⟨⟨f,?_⟩,inj⟩⟩
  rintro u w ⟨diff,⟨_,d⟩ | ⟨_,d⟩⟩
  · exact ⟨fun eq => diff (inj eq),Or.inl ⟨rfl,d⟩⟩
  · exact ⟨fun eq => diff (inj eq),Or.inr ⟨rfl,d⟩⟩

/-- The single-star forcing obligation on the same host at any legal pair. -/
theorem row_forces_star_pair {X : Type*} (G : SimpleGraph X) {s t r : ℕ}
    (n m : ℕ → ℕ) (row : ForcingRow G s t n m r)
    (i : Fin s) (j : Fin t) (hr : i.val+j.val=r) :
    Forces G (oneStar (n i.val)) (oneStar (m j.val)) := by
  have ni : 0<s-i.val := by have := i.isLt; omega
  have mj : 0<t-j.val := by have := j.isLt; omega
  have h := row i.val j.val (s-i.val) (t-j.val) hr (by have := i.isLt; omega)
    (by have := j.isLt; omega) ni mj
  intro C hc
  rcases h C hc with a | b
  · let v : Fin (s-i.val) := ⟨0,ni⟩
    have inRow := oneStar_in_forest (fun a : Fin (s-i.val) => n (i.val+a.val)) v
    simpa [v] using Or.inl (b := (oneStar (m j.val)).IsContained (G \ C)) (inRow.trans a)
  · let v : Fin (t-j.val) := ⟨0,mj⟩
    have inRow := oneStar_in_forest (fun a : Fin (t-j.val) => m (j.val+a.val)) v
    simpa [v] using Or.inr (a := (oneStar (n i.val)).IsContained C) (inRow.trans b)

/-- A nonempty zero-based antidiagonal has an original pair attaining its maximum. -/
theorem diagonal_attained {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hs : 0<s) (ht : 0<t) (r : ℕ) (live : r<s+t-1) :
    ∃ (i : Fin s) (j : Fin t), i.val+j.val = r ∧
      diagonal n m (r+2) = n i + m j - 1 := by
  let S := (Finset.univ : Finset (Fin s × Fin t)).filter
    (fun p => (p.1.val + 1) + (p.2.val + 1) = r+2)
  let i : Fin s := ⟨min r (s-1),by omega⟩
  let j : Fin t := ⟨r-i.val,by dsimp [i]; omega⟩
  have hh : (i,j) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by dsimp [j,i]; omega⟩
  obtain ⟨⟨a,b⟩,mem,eq⟩ := Finset.exists_mem_eq_sup S ⟨_,hh⟩ (fun p => n p.1 + m p.2 - 1)
  have sum := (Finset.mem_filter.mp mem).2
  change (a.val+1)+(b.val+1)=r+2 at sum
  exact ⟨a,b,by omega,eq⟩

#print axioms row_forces_star_pair
#print axioms diagonal_attained
end JSP452Audit.StarHost
