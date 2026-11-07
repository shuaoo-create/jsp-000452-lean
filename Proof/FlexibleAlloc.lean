import BinaryFlexDef
namespace JSP452Audit.StarHost
open SimpleGraph
private theorem fill_bounded {I : Type*} [DecidableEq I] (z : I → ℕ) (T : Finset I) :
    ∀ u, u≤∑i∈T,z i → ∃ f : I→ℕ, (∀i,f i≤z i) ∧ ∑i∈T,f i=u := by
  induction T using Finset.induction_on with
  | empty =>
    intro u h
    exact ⟨fun _ => 0,fun _ => Nat.zero_le _,by simp at h ⊢; omega⟩
  | @insert k T fresh ih =>
    intro u h
    rw [Finset.sum_insert fresh] at h
    let v := min u (z k)
    obtain ⟨f,bound,total⟩ := ih (u-v) (by dsimp [v]; omega)
    let g (i : I) := if i=k then v else f i
    have sub (i : I) : g i ≤ z i := by
      by_cases eq : i=k
      · subst i; simp [g,v]
      · simpa [g,eq] using bound i
    have rest : (∑i∈T,g i) = ∑i∈T,f i :=
      Finset.sum_congr rfl (fun i hi => if_neg (fun (eq : i=k) => fresh (eq ▸ hi)))
    refine ⟨g,sub,?_⟩
    rw [Finset.sum_insert fresh,rest,total]
    change (if k=k then v else f k) + _=_
    rw [if_pos rfl]; dsimp [v]; omega

theorem flexible_allocation {I : Type*} [Fintype I] [DecidableEq I] (z : I→ℕ)
    (flex : I→Prop) [DecidablePred flex] (small : ∀i,z i≤3)
    (ample : 2≤∑i,if flex i then z i else 0) (u : ℕ) (le : u≤∑i,z i) :
    ∃ r : I→ℕ, (∀i,r i≤z i) ∧ (∀i,¬flex i → r i=0 ∨ r i=z i) ∧ ∑i,r i=u := by
  let good (i : I) := if flex i then z i else 0
  let bad (i : I) := if flex i then 0 else z i
  have each i : good i + bad i = z i := by by_cases h : flex i <;> simp [good,bad,h]
  have sum : (∑i,good i)+(∑i,bad i)=∑i,z i := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _ => each i)
  have enough : 2≤∑i,good i := ample
  have cap i : bad i≤(∑j,good j)+1 := by have := small i; dsimp [bad]; split <;> omega
  obtain ⟨T,x,y,split⟩ := capacity_split bad u ((∑i,z i)-u) (∑i,good i) (by omega) cap
  obtain ⟨f,bound,filled⟩ := fill_bounded good Finset.univ (u-∑i∈T,bad i) (by omega)
  let r (i : I) := (if i∈T then bad i else 0)+f i
  refine ⟨r,?_,?_,?_⟩
  · intro i
    have a := each i; have b := bound i
    dsimp [r]; split <;> omega
  · intro i h
    have zero : f i=0 := by have := bound i; simp [good,h] at this; exact this
    dsimp [r,bad]; by_cases t : i∈T <;> simp [t,h,zero]
  · unfold r
    rw [Finset.sum_add_distrib,filled]
    have clip : (∑ i : I, if i∈T then bad i else 0)=∑i∈T,bad i := by
      rw [← Finset.sum_filter]; simp
    rw [clip]; omega
#print axioms flexible_allocation
end JSP452Audit.StarHost