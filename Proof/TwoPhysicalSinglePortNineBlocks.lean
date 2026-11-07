import UniqueActualPortAndOddOrder
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_has_two_actual_ports (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (nine:diagonal F.n F.m (F.r+2)-1=9) :
    ∃K:NineOriginalCut F.G,(highestWidth F.n F.m F.r:ℤ)≤K.eta ∧ K.S.ncard=K.T.ncard+1 ∧
      (∀J:NineOriginalCut F.G,J.eta≤K.eta) ∧
      (∀J:NineOriginalCut F.G,J.eta=K.eta → J.S.ncard+J.T.ncard≤K.S.ncard+K.T.ncard) ∧
      ∃(e:Fin 2↪↥K.onePortBlocks) (port:∀i,K.Port (e i).val),
        let A := Set.range (fun i => (port i).root)
        A⊆K.S ∧ 1≤A.ncard ∧ A.ncard≤2 ∧
          (rootShortfall F.G A 9:ℤ)+2*((F.G.induce A).edgeSet.ncard:ℤ)+K.eta≤6 ∧
          ∀i,Odd (Nat.card (e i).val.val.supp) ∧ 11≤Nat.card (e i).val.val.supp := by
  classical
  obtain ⟨K,width,_,gap,_,best,large⟩ := strict_nine_maximal_cut F paid nine
  have hp := (strict_nine_original_peak F paid nine).1
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤9 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  have fee := K.one_port_lower_bound cap
  let _ := Fintype.ofFinite ↥K.onePortBlocks
  have fit : Fintype.card (Fin 2)≤Fintype.card ↥K.onePortBlocks := by
    rw [Fintype.card_fin,←Nat.card_eq_fintype_card];change 2≤K.onePortBlocks.ncard;omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le fit
  let port (i:Fin 2) := (K.unique_physical_port (e i).val (e i).property).some
  let A := Set.range (fun i => (port i).root)
  have sub : A⊆K.S := by rintro _ ⟨i,rfl⟩;exact (port i).root_mem
  let f (i:Fin 2) : A := ⟨(port i).root,i,rfl⟩
  have onto : Function.Surjective f := by rintro ⟨_,i,rfl⟩;exact ⟨i,rfl⟩
  have upper := Nat.card_le_card_of_surjective f onto
  rw [Nat.card_fin] at upper
  have pos : 0<A.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨(port 0).root,0,rfl⟩
  exact ⟨K,width,gap,best,large,e,port,sub,pos,upper,K.root_debt_with_internal_edges cap gap A sub,
    fun i => K.actual_one_port_order cap (e i).val (e i).property⟩

#print axioms strict_nine_has_two_actual_ports
end JSP452Audit.StarHost
