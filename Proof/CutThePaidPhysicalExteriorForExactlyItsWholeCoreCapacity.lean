import SixLateColumnsPayTheFullFirstColumnAndTheUniqueSmallException
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
universe u

theorem full_capacity_prefix_data (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤0) :
    let Z := P.capacity
    let N := P.paidCore.ncard
    let z := P.positives.ncard
    N=2*Z+z ∧ 2*z≤Z ∧ 5*N≤11*Z ∧ 16*N≤35*Z ∧ 0<Z ∧ Z≤P.exterior.ncard ∧
      ∀Q:↥P.positives,matchingEdges Q.val.toSimpleGraph≤Z := by
  classical
  intro Z N z
  let D := diagonal F.n F.m (F.r+2)-1
  let h := highestWidth F.n F.m F.r
  have low : 11≤D := strict_source_degree_at_least_eleven F paid
  obtain ⟨_,_,_,count,weight,order⟩ := P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 h
  change N=2*Z+z at order
  have volume : D*z≤2*Z := by exact_mod_cast count
  have floor := (Nat.mul_le_mul_right z low).trans volume
  change (P.shortfall:ℤ)+(F.G.induce P.cutRoots).edgeSet.ncard+h-P.weight≤0 at credit
  have pos : 0<Z := by change P.weight≤(Z:ℤ) at weight;change 0<h at hp;omega
  obtain ⟨len,out,_,_⟩ := strict_payable_exterior_constraints F paid P
  have room := minUnmatched_add_twice_matching (F.G.induce P.exterior)
  rw [Nat.card_coe_set_eq] at room
  change Z+_+_+1≤min F.s F.t at len
  refine ⟨order,by omega,by omega,by omega,pos,by omega,?_⟩
  intro Q
  let C := F.G.induce P.paidCore
  let _ := Fintype.ofFinite C.ConnectedComponent
  let e := coreComponentEquiv F.G K.barrier P.positives
  let L := e.symm Q
  have label : e L=Q := e.apply_symm_apply Q
  have eq := rank_eq_of_graph_iso (coreComponentIso F.G K.barrier P.positives L)
  change matchingEdges L.toSimpleGraph=matchingEdges (e L).val.toSimpleGraph at eq
  rw [label] at eq
  rw [←eq]
  change _≤matchingEdges C
  rw [core_component_menu_totals C]
  exact Finset.single_le_sum (f:=fun i:C.ConnectedComponent => matchingEdges i.toSimpleGraph) (fun _ _ => Nat.zero_le _) (Finset.mem_univ L)

#print axioms full_capacity_prefix_data
end JSP452Audit.StarHost
