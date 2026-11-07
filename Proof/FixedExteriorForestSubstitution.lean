import RecombineForestCopiesOnSum
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
namespace JSP452Audit.StarHost
open SimpleGraph

def PreservesSmallForests {X Y : Type*} (C : SimpleGraph X) (B : SimpleGraph Y) (h : ℕ) : Prop :=
  ∀ (I:Type) [Fintype I] (n:I→ℕ), (∀i,1≤n i) → (∀i,n i≤h) → (forest n).IsContained C → (forest n).IsContained B

def SimulatesSmallForests {X Y : Type*} (C : SimpleGraph X) (J : SimpleGraph Y) (h : ℕ) : Prop :=
  ∀P:SimpleGraph Y,P≤J → ∃A:SimpleGraph X,A≤C ∧
    PreservesSmallForests A P h ∧ PreservesSmallForests (C \ A) (J \ P) h

theorem preserved_on_fixed_exterior {X Y Z : Type*} (B : SimpleGraph X) (C : SimpleGraph Y)
    (P : SimpleGraph Z) (h : ℕ) (keep : PreservesSmallForests C P h)
    {I : Type} [Fintype I] (n : I→ℕ) (pos : ∀i,1≤n i) (cap : ∀i,n i≤h)
    (copy : (forest n).IsContained (B ⊕g C)) : (forest n).IsContained (B ⊕g P) := by
  classical
  obtain ⟨U,left,right⟩ := split_copy_on_sum B C n copy
  have fin : Fintype ↥(Uᶜ : Set I) := Fintype.ofFinite _
  exact recombine_forest_copies B P n U left (keep _ _ (fun i => pos i.val) (fun i => cap i.val) right)

theorem substitute_fixed_exterior_row {X Y Z : Type*}
    (B : SimpleGraph X) (C : SimpleGraph Y) (J : SimpleGraph Z) (h : ℕ) (sim : SimulatesSmallForests C J h)
    {s t r : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (pn : ∀i,1≤n i) (pm : ∀i,1≤m i)
    (hn : ∀i,n i≤h) (hm : ∀i,m i≤h) (row : ForcingRow (B ⊕g C) s t (padDemand n) (padDemand m) r) :
    ForcingRow (B ⊕g J) s t (padDemand n) (padDemand m) r := by
  intro i j l q idx il jq pl pq R sub
  let E := R.comap Sum.inl
  let P := R.comap Sum.inr
  have exterior : E≤B := fun _ _ edge => sub edge
  have interior : P≤J := fun _ _ edge => sub edge
  have split : E ⊕g P=R := by
    ext a b
    cases a <;> cases b
    · rfl
    · exact ⟨fun e => (not_adj_sum_inl_inr _ _ e).elim,fun e => (not_adj_sum_inl_inr _ _ (sub e)).elim⟩
    · exact ⟨fun e => (not_adj_sum_inl_inr _ _ e.symm).elim,fun e => (not_adj_sum_inl_inr _ _ (sub e).symm).elim⟩
    · rfl
  obtain ⟨A,ac,red,blue⟩ := sim P interior
  obtain ⟨both,comp⟩ := JSP452Audit.StarHost.sum_colors exterior ac
  have compl := (JSP452Audit.StarHost.sum_colors exterior interior).2
  rw [split] at compl
  rcases row i j l q idx il jq pl pq _ both with first|second
  · left
    rw [←split]
    apply preserved_on_fixed_exterior E A P h red (fun z:Fin l => padDemand n (i+z.val)) _ _ first
    · exact fun z => pad_positive n pn _ (by have := z.isLt;omega)
    · intro z
      have inList : i+z.val<s := by have := z.isLt;omega
      simpa [padDemand,inList] using hn ⟨_,inList⟩
  · right
    rw [comp] at second
    rw [compl]
    apply preserved_on_fixed_exterior (B \ E) (C \ A) (J \ P) h blue (fun z:Fin q => padDemand m (j+z.val)) _ _ second
    · exact fun z => pad_positive m pm _ (by have := z.isLt;omega)
    · intro z
      have inList : j+z.val<t := by have := z.isLt;omega
      simpa [padDemand,inList] using hm ⟨_,inList⟩

#print axioms preserved_on_fixed_exterior
#print axioms substitute_fixed_exterior_row
end JSP452Audit.StarHost
