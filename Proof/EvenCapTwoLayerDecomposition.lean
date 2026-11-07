import SafeColorQuotasAtAnyCap
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

structure TwoDegreeLayers {X:Type u} [Finite X] (G:SimpleGraph X) (m:ℕ) where
  part : Fin m→SimpleGraph X
  sub : ∀i,part i≤G
  cover : ∀x y,G.Adj x y → ∃i,(part i).Adj x y
  unique : ∀i j x y,(part i).Adj x y → (part j).Adj x y → i=j
  cap : ∀i v,Nat.card ((part i).neighborSet v)≤2
  total : ∀v,(∑i:Fin m,((part i).neighborSet v).ncard)=(G.neighborSet v).ncard

theorem actual_even_cap_layers (m:ℕ) : ∀{X:Type u} [Finite X] (G:SimpleGraph X),
    (∀v,Nat.card (G.neighborSet v)≤2*m) → Nonempty (TwoDegreeLayers G m) := by
  induction m with
  | zero =>
    intro X _ G bound
    have edgeless {x y:X} (edge:G.Adj x y) : False := by
      have pos := (Set.ncard_pos (G.neighborSet x).toFinite).mpr (show (G.neighborSet x).Nonempty from ⟨y,edge⟩)
      have none : (G.neighborSet x).ncard≤0 := bound x;omega
    refine ⟨⟨Fin.elim0,fun i => i.elim0,fun _ _ e => (edgeless e).elim,fun i => i.elim0,
      fun i => i.elim0,?_⟩⟩
    intro v
    have none : (G.neighborSet v).ncard≤0 := bound v
    simp only [Finset.univ_eq_empty,Finset.sum_empty];omega
  | succ m ih =>
    intro X _ G bound
    obtain ⟨R,sub,caps⟩ := even_even_degree_split G 1 m (fun v => by rw [Nat.add_comm 1 m];exact bound v)
    obtain ⟨V⟩ := ih (G \ R) (fun v => (caps v).2)
    let P : Fin (m+1)→SimpleGraph X := Fin.cons R V.part
    refine ⟨⟨P,?_,?_,?_,?_,?_⟩⟩
    · intro i;refine Fin.cases sub (fun j => (V.sub j).trans sdiff_le) i
    · intro x y edge
      by_cases first:R.Adj x y
      · exact ⟨0,first⟩
      · obtain ⟨j,e⟩ := V.cover x y ⟨edge,first⟩;exact ⟨j.succ,e⟩
    · intro i j
      refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
      · intro _ _ _ _;rfl
      · intro x y r e;exact ((V.sub b e).2 r).elim
      · intro x y e r;exact ((V.sub a e).2 r).elim
      · intro x y ea eb;exact congrArg Fin.succ (V.unique a b x y ea eb)
    · intro i;exact Fin.cases (fun v => (caps v).1) (fun j => V.cap j) i
    · intro v
      rw [Fin.sum_univ_succ]
      change (R.neighborSet v).ncard+(∑j:Fin m,((V.part j).neighborSet v).ncard)=(G.neighborSet v).ncard
      rw [V.total];exact palette_neighbor_sum G R sub v

#print axioms actual_even_cap_layers
end JSP452Audit.StarHost
