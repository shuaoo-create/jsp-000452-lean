import SixOddComponentExposureClassification
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem odd_regular_extra_exposure {X:Type*} [Finite X] (G:SimpleGraph X)
    (D:ℕ) (C:G.ConnectedComponent) (member:C∈oddRegularComponents G D)
    (extra:3≤minimumExposure C.toSimpleGraph D) :
    (oddRegularComponents G D).ncard+2≤minimumExposure G D := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  let Z := oddRegularComponents G D
  have one (c:G.ConnectedComponent) (mem:c∈Z) : 1≤minimumExposure c.toSimpleGraph D := by
    obtain ⟨⟨k,odd⟩,full⟩ := mem
    have eq := regular_exposure_order_rank c.toSimpleGraph D
      (fun x => (component_degree_eq G c x).trans (full x.val x.property))
    change Nat.card c.supp=2*k+1 at odd
    change 2*matchingEdges c.toSimpleGraph+minimumExposure c.toSimpleGraph D=Nat.card c.supp at eq
    omega
  let base (c:G.ConnectedComponent) : ℕ := if c∈Z then 1 else 0
  let more (c:G.ConnectedComponent) : ℕ := if c=C then 2 else 0
  have per (c:G.ConnectedComponent) : base c+more c≤minimumExposure c.toSimpleGraph D := by
    dsimp [base,more]
    by_cases same : c=C
    · subst c
      simp only [if_pos (show C∈Z from member),if_true];exact extra
    · rw [if_neg same,Nat.add_zero]
      split_ifs with mem
      · exact one c mem
      · exact Nat.zero_le _
  have total := Finset.sum_le_sum (s:=(Finset.univ:Finset G.ConnectedComponent)) (fun c _ => per c)
  rw [Finset.sum_add_distrib,←minimumExposure_component_total] at total
  have count : (∑c:G.ConnectedComponent,base c)=Z.ncard := by simp [base,Finset.sum_boole,Set.ncard_eq_toFinset_card']
  have two : (∑c:G.ConnectedComponent,more c)=2 := by simp [more]
  rwa [count,two] at total

theorem strict_six_true_component_capacity (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (C:F.G.ConnectedComponent) (mem:C∈oddRegularComponents F.G 6) :
    let z := matchingEdges C.toSimpleGraph
    4≤z ∧ Nat.card C.supp=2*z+1 ∧ minimumExposure C.toSimpleGraph 6=1 ∧ C.toSimpleGraph.edgeSet.ncard=6*z+3 := by
  intro z
  let c := (oddRegularComponents F.G 6).ncard
  let ρ := minimumExposure F.G 6
  obtain ⟨single,multiple⟩ := strict_six_component_exposure_classes F paid six
  have positive : 1≤c := (strict_six_real_component_bounds F paid six).1.trans (strict_six_original_odd_regular F paid six)
  change (c=1 → ρ≤2) at single
  change (2≤c → c=ρ) at multiple
  have upper : ρ≤c+1 := by
    by_cases small : c=1
    · have := single small;omega
    · have common := multiple (by omega : 2≤c);omega
  have reg (v:C.supp) := (component_degree_eq F.G C v).trans (mem.2 v.val v.property)
  have account := regular_exposure_order_rank C.toSimpleGraph 6 reg
  change 2*z+minimumExposure C.toSimpleGraph 6=Nat.card C.supp at account
  obtain ⟨k,odd⟩ := mem.1
  have tiny : minimumExposure C.toSimpleGraph 6≤2 := by
    by_contra! big
    have ex := odd_regular_extra_exposure F.G 6 C mem big
    change c+2≤ρ at ex
    omega
  have exactOne : minimumExposure C.toSimpleGraph 6=1 := by omega
  have order := strict_six_odd_regular_order F paid six C mem
  have mass := degree_sum_full C.toSimpleGraph Set.univ 6 (fun v _ => reg v)
  have hand := degree_sum_complement C.toSimpleGraph Set.univ
  have zero : originalDegreeSum C.toSimpleGraph ∅=0 := by simp [originalDegreeSum]
  rw [Set.compl_univ,zero,Nat.add_zero,mass,Set.ncard_univ] at hand
  change 6*Nat.card C.supp=2*C.toSimpleGraph.edgeSet.ncard at hand
  exact ⟨by omega,by omega,exactOne,by omega⟩

#print axioms odd_regular_extra_exposure
#print axioms strict_six_true_component_capacity
end JSP452Audit.StarHost
