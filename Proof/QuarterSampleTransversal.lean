import QuarterExteriorCharge
namespace JSP452Audit.StarHost

private theorem nat_indicator {A : Type*} [Fintype A] (cond : A→Prop) [DecidablePred cond] :
    (∑a:A,if cond a then (1:ℕ) else 0)=Nat.card {a // cond a} := by
  rw [Finset.sum_boole,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rfl

private theorem sum_incidence_counts {L T : Type*} [Fintype L] [Fintype T] (P : L→T→Prop) :
    (∑l:L,({t | P l t}:Set T).ncard) = ∑t:T,Nat.card {l // P l t} := by
  classical
  calc
    _ = ∑l:L,∑t:T,if P l t then 1 else 0 := by
      apply Finset.sum_congr rfl;intro l _
      rw [nat_indicator,←Nat.card_coe_set_eq]
      rfl
    _ = ∑t:T,∑l:L,if P l t then 1 else 0 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun t _ => nat_indicator _)

/-- Choose an actual transversal by sampling one in four labels and repairing
each missed set. The finite average is over all four-way functions. -/
theorem quarter_sample_transversal {V T : Type*} [Fintype V] [Fintype T] (N : T→Set V)
    (nonempty : ∀t,(N t).Nonempty) :
    ∃S:Set V,(∀t,∃v∈S,v∈N t) ∧
      (S.ncard:ℚ)≤(Nat.card V:ℚ)/4 + ∑t:T,(3/4:ℚ)^(N t).ncard := by
  classical
  let L := V→Fin 4
  let pick (f:L) := {v:V | f v=0}
  let miss (f:L) := {t:T | ∀v∈N t,f v≠0}
  let den : ℚ := 4^(Nat.card V)
  let bound : ℚ := (Nat.card V:ℚ)/4 + ∑t:T,(3/4:ℚ)^(N t).ncard
  have vNat := sum_incidence_counts (fun (f:L) (v:V) => f v=0)
  have tNat := sum_incidence_counts (fun (f:L) (t:T) => ∀v∈N t,f v≠0)
  have pickSum : (∑f:L,((pick f).ncard:ℚ))=den*((Nat.card V:ℚ)/4) := by
    have cast : (∑f:L,((pick f).ncard:ℚ))=∑v:V,(Nat.card {f : L // f v=0}:ℚ) := by exact_mod_cast vNat
    rw [cast,Finset.sum_congr rfl (fun (v:V) (_ : v∈Finset.univ) => selected_quarter_weight v)]
    rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul];dsimp [den];ring
  have missSum : (∑f:L,((miss f).ncard:ℚ))=den*(∑t:T,(3/4:ℚ)^(N t).ncard) := by
    have cast : (∑f:L,((miss f).ncard:ℚ))=∑t:T,(Nat.card {f : L // ∀v∈N t,f v≠0}:ℚ) := by exact_mod_cast tNat
    rw [cast,Finset.sum_congr rfl (fun (t:T) (_ : t∈Finset.univ) => missed_quarter_weight (N t)),←Finset.mul_sum]
  have card : (Fintype.card L:ℚ)=den := by
    rw [←Nat.card_eq_fintype_card];change (Nat.card (V→Fin 4):ℚ)=_
    rw [Nat.card_fun,Nat.card_fin];push_cast;rfl
  have good : ∃f:L,((pick f).ncard:ℚ)+(miss f).ncard≤bound := by
    by_contra! none
    let zero : L := fun _ => 0
    have lt := Finset.sum_lt_sum (s:=(Finset.univ : Finset L)) (fun f _ => (none f).le)
      ⟨zero,Finset.mem_univ _,none zero⟩
    have total : (∑f:L,(((pick f).ncard:ℚ)+(miss f).ncard))=den*bound := by
      rw [Finset.sum_add_distrib,pickSum,missSum,←mul_add]
    have constant : (∑_f:L,bound)=den*bound := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card]
    rw [constant,total] at lt;exact (lt_irrefl _ lt)
  obtain ⟨f,small⟩ := good
  choose rescue legal using nonempty
  let S := pick f∪(rescue '' miss f)
  have size := (Set.ncard_union_le (pick f) (rescue '' miss f)).trans
    (Nat.add_le_add_left (Set.ncard_image_le (f:=rescue) (s:=miss f)) _)
  have real : (S.ncard:ℚ)≤((pick f).ncard:ℚ)+(miss f).ncard := by exact_mod_cast size
  refine ⟨S,?_,real.trans small⟩
  intro t
  by_cases hits : ∃v∈N t,f v=0
  · obtain ⟨v,hv,chosen⟩ := hits;exact ⟨v,Or.inl chosen,hv⟩
  have mt : t∈miss f := fun v hv chosen => hits ⟨v,hv,chosen⟩
  exact ⟨rescue t,Or.inr ⟨t,mt,rfl⟩,legal t⟩

#print axioms quarter_sample_transversal
end JSP452Audit.StarHost
