import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

/- Greedy path for the star-forest host of Erdős #561. This module speaks
   only about numerical capacities, not graphs, embeddings of stars, or Ramsey numbers. -/
namespace JSP452Audit.UpperPath

/-- Indices are strictly increasing, lie in [start, stop), and meet their
    respective demands in the order in which the list gives them. -/
def Selected (demand : List ℕ) (cap : ℕ → ℕ) (start stop : ℕ) : Prop :=
  ∃ indices : List ℕ, indices.Pairwise (· < ·) ∧
    (∀ k ∈ indices, start ≤ k ∧ k < stop) ∧
    List.Forall₂ (fun d k => d ≤ cap k) demand indices

private theorem emptySelected (cap : ℕ → ℕ) (start stop : ℕ) : Selected [] cap start stop :=
  ⟨[], .nil, by simp, .nil⟩

private theorem skip {demand cap start stop} (sel : Selected demand cap (start+1) stop) :
    Selected demand cap start stop := by
  obtain ⟨ids,hp,hb,hd⟩ := sel
  exact ⟨ids,hp,fun k hk => ⟨Nat.le_trans (Nat.le_succ _) (hb k hk).1,(hb k hk).2⟩,hd⟩

private theorem takeHead {demand cap start stop d} (fits : d ≤ cap start) (room : start < stop)
    (sel : Selected demand cap (start+1) stop) : Selected (d::demand) cap start stop := by
  obtain ⟨ids,hp,hb,hd⟩ := sel
  refine ⟨start::ids, List.pairwise_cons.mpr ⟨fun k hk => (hb k hk).1,hp⟩, ?_, .cons fits hd⟩
  intro k hk
  rcases List.mem_cons.mp hk with h | h
  · subst k; exact ⟨Nat.le_refl start,room⟩
  · exact ⟨Nat.le_trans (Nat.le_succ _) (hb k h).1,(hb k h).2⟩

private theorem selectAux (r b : List ℕ) (red blue : ℕ → ℕ) (start stop : ℕ)
    (room : start + r.length + b.length ≤ stop + 1)
    (step : ∀ (i j : ℕ) (hi : i < r.length) (hj : j < b.length),
      r[i] ≤ red (start+i+j) ∨ b[j] ≤ blue (start+i+j)) :
    Selected r red start stop ∨ Selected b blue start stop := by
  induction r generalizing b start with
  | nil => exact Or.inl (emptySelected red start stop)
  | cons a as hr =>
    induction b generalizing start with
    | nil => exact Or.inr (emptySelected blue start stop)
    | cons c cs hb =>
      have space : start < stop := by simp only [List.length_cons] at room; omega
      have now := step 0 0 (by simp) (by simp)
      simp only [Nat.add_zero,List.getElem_cons_zero] at now
      rcases now with ha | hc
      · have rest := hr (c::cs) (start+1) (by simp only [List.length_cons] at room ⊢; omega)
          (by
            intro i j hi hj
            have hh := step (i+1) j (by simpa using hi) hj
            simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh)
        exact rest.elim (fun h => Or.inl (takeHead ha space h)) (fun h => Or.inr (skip h))
      · have rest := hb (start+1) (by simp only [List.length_cons] at room ⊢; omega)
          (by
            intro i j hi hj
            have hh := step i (j+1) hi (by simpa using hj)
            simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh)
        exact rest.elim (fun h => Or.inl (skip h)) (fun h => Or.inr (takeHead hc space h))

/-- At component k=i+j one of the next two demands can be met. Then one full
    colour list is selected inside the first r.length+b.length-1 components. -/
theorem select (r b : List ℕ) (red blue : ℕ → ℕ)
    (step : ∀ (i j : ℕ) (hi : i < r.length) (hj : j < b.length),
      r[i] ≤ red (i+j) ∨ b[j] ≤ blue (i+j)) :
    Selected r red 0 (r.length + b.length - 1) ∨
    Selected b blue 0 (r.length + b.length - 1) := by
  apply selectAux <;> first | omega | simpa using step

private theorem indicesToFin {s n : ℕ} (demand : Fin s → ℕ) (cap : ℕ → ℕ)
    (sel : Selected (List.ofFn demand) cap 0 n) :
    ∃ f : Fin s → Fin n, StrictMono f ∧ ∀ i, demand i ≤ cap (f i).val := by
  obtain ⟨ids,hp,hb,hd⟩ := sel
  have len : s = ids.length := by simpa using hd.length_eq
  let pos (i : Fin s) : Fin ids.length := ⟨i.val,len ▸ i.isLt⟩
  let f (i : Fin s) : Fin n := ⟨ids.get (pos i), (hb _ (List.get_mem ids (pos i))).2⟩
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    exact hp.rel_get_of_lt (a := pos i) (b := pos j) hij
  · intro i
    have h := hd.get (i := i.val) (by simp) (pos i).isLt
    simpa [List.get_ofFn, f, pos] using h

/-- Zero-based host index: the same pair has one-based diagonal (i+1)+(j+1). -/
def hostIndex {s t : ℕ} (i : Fin s) (j : Fin t) : Fin (s+t-1) :=
  ⟨i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩

/-- Finite-coordinate form for assigning star centers to different host stars. -/
theorem selectFin {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ)
    (red blue : Fin (s+t-1) → ℕ)
    (step : ∀ i j, n i ≤ red (hostIndex i j) ∨ m j ≤ blue (hostIndex i j)) :
    (∃ f : Fin s → Fin (s+t-1), StrictMono f ∧ ∀ i, n i ≤ red (f i)) ∨
    (∃ f : Fin t → Fin (s+t-1), StrictMono f ∧ ∀ j, m j ≤ blue (f j)) := by
  let cap (c : Fin (s+t-1) → ℕ) (k : ℕ) := if h : k < s+t-1 then c ⟨k,h⟩ else 0
  have sel := select (List.ofFn n) (List.ofFn m) (cap red) (cap blue) (by
    intro i j hi hj
    have his : i < s := by simpa using hi
    have hjt : j < t := by simpa using hj
    have hk : i+j < s+t-1 := by omega
    simpa [cap,hk,hostIndex] using step ⟨i,his⟩ ⟨j,hjt⟩)
  simp only [List.length_ofFn] at sel
  rcases sel with h | h
  · obtain ⟨f,hf,hs⟩ := indicesToFin n (cap red) h
    exact Or.inl ⟨f,hf,fun i => by simpa [cap,(f i).isLt] using hs i⟩
  · obtain ⟨f,hf,hs⟩ := indicesToFin m (cap blue) h
    exact Or.inr ⟨f,hf,fun j => by simpa [cap,(f j).isLt] using hs j⟩

/-- A host of size at least nᵢ+mⱼ−1 meets the step hypothesis once its leaves
    are counted in two colors. Positive target sizes suffice; no ordering needed. -/
theorem selectFin_of_total {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ)
    (red blue : Fin (s+t-1) → ℕ)
    (size : ∀ i j, n i + m j - 1 ≤ red (hostIndex i j) + blue (hostIndex i j)) :
    (∃ f : Fin s → Fin (s+t-1), StrictMono f ∧ ∀ i, n i ≤ red (f i)) ∨
    (∃ f : Fin t → Fin (s+t-1), StrictMono f ∧ ∀ j, m j ≤ blue (f j)) := by
  apply selectFin n m red blue
  intro i j
  have := size i j
  omega

#print axioms select
#print axioms selectFin
#print axioms selectFin_of_total
end JSP452Audit.UpperPath
