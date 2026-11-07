import CompleteExteriorMixedSurplus
import TwoTripleRootAssignment
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Each position of a decreasing target has enough distinct eligible
labels in the same actual (possibly unsorted) surviving forest. -/
theorem labels_of_thresholds {l : ℕ} {J : Type*} [Fintype J] (n : Fin l→ℕ) (m : J→ℕ)
    (enough : ∀i,i.val+1≤(Finset.univ.filter (fun z => n i≤m z)).card) :
    ∃f:Fin l ↪ J,∀i,n i≤m (f i) := by
  classical
  let nbr (i:Fin l) := Finset.univ.filter (fun z:J => n i≤m z)
  have hall (S:Finset (Fin l)) : S.card≤(S.biUnion nbr).card := by
    by_cases non : S.Nonempty
    · let i := S.max' non
      have card : S.card≤ i.val+1 := by
        let f : ↥S → Fin (i.val+1) := fun z => ⟨z.val.val,Nat.lt_succ_of_le (S.le_max' _ z.property)⟩
        have bound := Fintype.card_le_of_injective f (fun a b eq => Subtype.ext (Fin.ext (congrArg (fun z : Fin (i.val+1) => z.val) eq)))
        simpa using bound
      have incl : nbr i⊆S.biUnion nbr := fun _ mem => Finset.mem_biUnion.mpr ⟨i,S.max'_mem non,mem⟩
      exact card.trans ((enough i).trans (Finset.card_le_card incl))
    · rw [Finset.not_nonempty_iff_eq_empty.mp non];simp
  obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' nbr).mp hall
  exact ⟨⟨f,inj⟩,fun i => (Finset.mem_filter.mp (mem i)).2⟩

/-- Removing at most b damaged labels from a collection of q distinct
eligible locations still certifies q-b distinct witnesses in the same list. -/
theorem many_after_exceptions {J : Type*} [Fintype J] {q b : ℕ} (f : Fin q ↪ J)
    (bad : Finset J) (price : bad.card≤b) (val : J→ℕ) (h : ℕ)
    (fit : ∀i,f i∉bad → h≤val (f i)) :
    q-b≤(Finset.univ.filter (fun x => h≤val x)).card := by
  classical
  let chosen := Finset.univ.map f
  have size : chosen.card=q := by simp [chosen]
  have cut := Finset.card_sdiff_add_card_inter chosen bad
  have lost := Finset.card_le_card (Finset.inter_subset_right : chosen∩bad⊆bad)
  have sub : chosen \ bad ⊆ Finset.univ.filter (fun x => h≤val x) := by
    intro x hx
    obtain ⟨pick,good⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp pick
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fit i good⟩
  have lower := Finset.card_le_card sub;omega

/-- Changing the a largest residual heads to ones and reordering gives
max(1,L[k+a]). Join this with the original mu-shifted tail, keeping the
residual list's full length. -/
noncomputable def commonErasedDemand {s : ℕ} (n : Fin s→ℕ) (W : RemovalBudget s) (a μ : ℕ) (i : Fin W.len) : ℕ :=
  max (max 1 (padDemand (W.entries n) (i.val+a))) (padDemand n (i.val+μ))

theorem common_erased_antitone {s : ℕ} (n : Fin s→ℕ) (hn : Antitone n) (W : RemovalBudget s) (a μ : ℕ) :
    Antitone (commonErasedDemand n W a μ) := by
  intro i j le
  exact max_le_max (max_le_max le_rfl (pad_antitone _ (W.entries_antitone n hn) (Nat.add_le_add_right le a)))
    (pad_antitone n hn (Nat.add_le_add_right le μ))

theorem common_erased_positive {s : ℕ} (n : Fin s→ℕ) (W : RemovalBudget s) (a μ : ℕ)
    (i:Fin W.len) : 1≤commonErasedDemand n W a μ i :=
  (le_max_left 1 _).trans (le_max_left _ _)

#print axioms labels_of_thresholds
#print axioms many_after_exceptions
#print axioms common_erased_antitone
end JSP452Audit.StarHost
