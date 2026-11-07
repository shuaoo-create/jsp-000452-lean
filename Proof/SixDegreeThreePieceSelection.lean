import ThreePiecesSupplySixDegreeVertices
namespace JSP452Audit.StarHost
open SimpleGraph

theorem omit_three_highest_capacities {I:Type*} [Fintype I] [DecidableEq I]
    (z:I→ℕ) (w:I→ℤ) (cap:∀i,w i≤3) (heavy:9<∑i,w i) :
    ∃T:Finset I,Tᶜ.card=3 ∧ (∀y∈Tᶜ,∀x∈T,z x≤z y) ∧
      (∑i,w i)≤(∑i∈T,w i)+9 ∧ ∃c∈T,∀x∈T,z x≤z c := by
  have bound := Finset.sum_le_sum (s:=(Finset.univ:Finset I)) (fun i _ => cap i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at bound
  have dummy : (2:ℤ)*(2+1)<∑_i:I,(2:ℤ) := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    omega
  obtain ⟨T,_,size,ord,_,last⟩ := heavy_piece_selection z (fun _ => (2:ℤ)) 2 (fun _ => by decide)
    (fun _ => le_rfl) dummy
  have removed := Finset.sum_le_sum (s:=Tᶜ) (fun i _ => cap i)
  simp only [Finset.sum_const,size,nsmul_eq_mul] at removed
  have all := Finset.sum_add_sum_compl T w
  exact ⟨T,size,ord,by omega,last⟩

theorem six_selected_outside {X:Type*} [Finite X] {G:SimpleGraph X} (K:DegreeRegion G 6)
    [Fintype ↥K.positive] [DecidableEq ↥K.positive] (T:Finset ↥K.positive) (Z b:ℕ)
    (many:Tᶜ.card=3) (floor:∀c∈Tᶜ,Z≤K.pieceCapacity c)
    (cap:∀v,Nat.card (G.neighborSet v)≤6) (need:b≤Z) :
    ∃U:Set X,U.ncard=b ∧ G.IsIndepSet U ∧ (∀v∈U,Nat.card (G.neighborSet v)=6) ∧
      ∀c∈T,∀⦃x y:X⦄,(wholePiece G K.barrier c.val).Adj x y → x∉U := by
  classical
  let outside := Subtype.val '' (↑(Tᶜ):Set ↥K.positive)
  have num : outside.ncard=3 := by rw [Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_coe_finset,many]
  have orders (c) (hc:c∈outside) : 2*Z+1≤Nat.card c.supp := by
    obtain ⟨w,mem,rfl⟩ := hc
    obtain ⟨v,hv⟩ := w.val.nonempty_supp
    have actual := factorCritical_order_rank w.val.toSimpleGraph (K.critical w.val).2 ⟨v,hv⟩
    change Nat.card w.val.supp=2*matchingEdges w.val.toSimpleGraph+1 at actual
    have bound := floor w mem
    change Z≤matchingEdges w.val.toSimpleGraph at bound
    omega
  obtain ⟨U,sub,ind,size⟩ := three_piece_independent_supply G K.barrier outside Z b num orders cap need
  have full : outside⊆{c|allFullComponent G K.barrier 6 c} := by
    rintro _ ⟨c,_,rfl⟩;exact K.full c.property.1
  refine ⟨U,size,ind,fun x mem => regionCore_full_degree G K.barrier outside 6 full (sub mem),?_⟩
  intro c hc x y edge hx
  obtain ⟨z,hz,rfl⟩ := ((wholePiece_adj G K.barrier c.val x y).mp edge).2.1
  obtain ⟨v,eq,w,mem,tag⟩ := sub hx
  have same : v=z := Subtype.ext eq
  subst v
  have label : (G.induce K.barrierᶜ).connectedComponentMk z=c.val := hz
  have equal : w=c := Subtype.ext (tag.trans label)
  exact (Finset.mem_compl.mp mem) (equal.symm ▸ hc)

#print axioms omit_three_highest_capacities
#print axioms six_selected_outside
end JSP452Audit.StarHost
