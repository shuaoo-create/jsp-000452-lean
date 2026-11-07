import BipartiteFullDegree
import Mathlib.Data.Finset.Sum
namespace JSP452Audit.StarHost

/-- Six labels split into two triples. Two neighbours per label and capacity
four per real root suffice for distinct assignments after allowing one
group-specific spare label in each triple, if at least four roots occur. -/
theorem two_triples_distinct_assignments {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]
    (colour : L→Bool) (adj : L→Finset R) (six : Fintype.card L=6)
    (triple : ∀b,(Finset.univ.filter (fun x => colour x=b)).card≤3)
    (two : ∀x,(adj x).card=2)
    (cap : ∀r,(Finset.univ.filter (fun x => r∈adj x)).card≤4)
    (roots : 4≤(Finset.univ.biUnion adj).card) :
    ∃f : L→R⊕Bool, Function.Injective f ∧
      (∀x r,f x=.inl r → r∈adj x) ∧ (∀x b,f x=.inr b → b=colour x) := by
  classical
  let Z (x:L) := (adj x).disjSum {colour x}
  have hall (T : Finset L) : T.card≤(T.biUnion Z).card := by
    let U := T.biUnion adj
    let V := T.image colour
    have eq : T.biUnion Z=U.disjSum V := by
      ext r
      cases r with
      | inl r => simp [Z,U]
      | inr b => simp [Z,V,Finset.mem_image,eq_comm]
    rw [eq,Finset.card_disjSum]
    by_cases nonempty : T.Nonempty
    · obtain ⟨x,hx⟩ := nonempty
      have inside (y:L) (hy:y∈T) : adj y⊆U := fun _ h => Finset.mem_biUnion.mpr ⟨_,hy,h⟩
      have lower : 2≤U.card := (two x).symm ▸ Finset.card_le_card (inside x hx)
      have vx : colour x∈V := Finset.mem_image_of_mem colour hx
      have vpos : 0<V.card := Finset.card_pos.mpr ⟨_,vx⟩
      have mixed : 4≤T.card → 2≤V.card := by
        intro many
        by_contra! few
        have v1 : V.card≤1 := by omega
        have sub : T⊆Finset.univ.filter (fun y => colour y=colour x) := by
          intro y hy
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.card_le_one.mp v1) _ (Finset.mem_image_of_mem colour hy) _ vx⟩
        exact (not_lt_of_ge ((Finset.card_le_card sub).trans (triple _))) (by omega)
      have fifth : 5≤T.card → 3≤U.card := by
        intro many
        by_contra! few
        obtain ⟨r,hr⟩ := Finset.card_pos.mp (show 0<U.card by omega)
        have sub : T⊆Finset.univ.filter (fun y => r∈adj y) := by
          intro y hy
          have same := Finset.eq_of_subset_of_card_le (inside y hy) (show U.card≤(adj y).card by rw [two];omega)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,same.symm ▸ hr⟩
        have lim := (Finset.card_le_card sub).trans (cap r)
        omega
      have total : T.card≤6 := Finset.card_le_univ T |>.trans_eq six
      by_cases all : T.card=6
      · have same : T=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [six,all])
        have four : 4≤U.card := by simpa [U,same] using roots
        have vm := mixed (by omega)
        omega
      by_cases five : T.card=5
      · have vm := mixed (by omega);have um := fifth (by omega);omega
      by_cases four : T.card=4
      · have vm := mixed (by omega);omega
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty];simp
  obtain ⟨f,inj,legal⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' Z).mp hall
  refine ⟨f,inj,?_,?_⟩
  · intro x r eq
    have h := legal x
    simpa [eq,Z] using h
  · intro x b eq
    have h := legal x
    simpa [eq,Z] using h

#print axioms two_triples_distinct_assignments
end JSP452Audit.StarHost
