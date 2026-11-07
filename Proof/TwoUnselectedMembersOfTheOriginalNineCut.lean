import SharperNinthColumnForSmallNinePortBoxes
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

theorem two_other_cut_members (cap : ∀v,Nat.card (G.neighborSet v)≤9) :
    ∃c d : ↥R.K.blocks,c≠(R.select 0).val ∧ c≠(R.select 1).val ∧
      d≠(R.select 0).val ∧ d≠(R.select 1).val ∧ c≠d ∧ R.K.sPorts c+R.K.tPorts c≤8 := by
  classical
  let _ := Fintype.ofFinite ↥R.K.blocks
  let M : Finset ↥R.K.blocks := {(R.select 0).val,(R.select 1).val}
  let J := Mᶜ
  let q := R.K.blocks.ncard
  let cost (c : ↥R.K.blocks) := R.K.sPorts c+R.K.tPorts c
  have ne : (R.select 0).val≠(R.select 1).val := fun eq =>
    (by decide : (0:Fin 2)≠1) (R.select.injective (Subtype.ext eq))
  have pair : M.card=2 := by simp [M,ne]
  have all : Fintype.card ↥R.K.blocks=q := by rw [←Nat.card_eq_fintype_card];rfl
  have card : J.card=q-2 := by rw [Finset.card_compl,all,pair]
  have totals := R.K.region_root_budgets cap
  have eq := uniform_factor_cut_on_original G 3 6 R.K.S R.K.T
  change R.K.eta=(q:ℤ)+(crossCount G R.K.T R.K.S:ℤ)-3*(R.K.S.ncard:ℤ)-6*(R.K.T.ncard:ℤ) at eq
  have sep := R.root_gap
  have positive := R.exposure
  have many : 4≤q := by omega
  have p := selected_cut_cross_sum G R.K.barrier R.K.blocks R.K.S
  have t := selected_cut_cross_sum G R.K.barrier R.K.blocks R.K.T
  change crossCount G R.K.region R.K.S=∑c:↥R.K.blocks,R.K.sPorts c at p
  change crossCount G R.K.region R.K.T=∑c:↥R.K.blocks,R.K.tPorts c at t
  have ceiling : (∑c:↥R.K.blocks,cost c)≤2*q+1 := by
    simp only [cost,Finset.sum_add_distrib,←p,←t];omega
  have inexpensive : ∃c∈J,cost c≤8 := by
    by_contra! no
    have need := Finset.sum_le_sum (s:=J) (f:=fun _ => 9) (g:=cost) (fun c h => no c h)
    change (∑_∈J,9)≤∑c∈J,cost c at need
    rw [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,card] at need
    have bound := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) (fun x _ _ => Nat.zero_le (cost x))
    omega
  obtain ⟨c,inside,small⟩ := inexpensive
  have other : (J.erase c).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem inside,card];omega)
  obtain ⟨d,mem⟩ := other
  have dm := Finset.mem_erase.mp mem
  have avoid (i : ↥R.K.blocks) (hi : i∈J) : i≠(R.select 0).val ∧ i≠(R.select 1).val := by
    have out : i∉M := Finset.mem_compl.mp hi
    simpa [M] using out
  exact ⟨c,d,(avoid c inside).1,(avoid c inside).2,(avoid d dm.2).1,(avoid d dm.2).2,dm.1.symm,small⟩

#print axioms two_other_cut_members
end JSP452Audit.StarHost.NinePortRegion
