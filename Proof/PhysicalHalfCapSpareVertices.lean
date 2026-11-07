import HalfCapSpareIndependentSet
namespace JSP452Audit.StarHost
open SimpleGraph

theorem half_cap_spare_vertices {X:Type*} [Finite X] {G:SimpleGraph X} (p:ℕ) (positive:0<p) (K:DegreeRegion G (2*p))
    [Fintype ↥K.positive] [DecidableEq ↥K.positive] (T:Finset ↥K.positive) (Z b:ℕ)
    (many:Tᶜ.card=p) (floor:∀c∈Tᶜ,Z≤K.pieceCapacity c)
    (cap:∀v,Nat.card (G.neighborSet v)≤2*p) (need:b≤Z) :
    ∃U:Set X,U.ncard=b ∧ G.IsIndepSet U ∧ (∀v∈U,Nat.card (G.neighborSet v)=2*p) ∧
      ∀c∈T,∀⦃x y:X⦄,(wholePiece G K.barrier c.val).Adj x y → x∉U := by
  classical
  let outside := Subtype.val '' (↑(Tᶜ):Set ↥K.positive)
  have num : outside.ncard=p := by rw [Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_coe_finset,many]
  have orders (c) (hc:c∈outside) : 2*Z+1≤Nat.card c.supp := by
    obtain ⟨w,mem,rfl⟩ := hc
    obtain ⟨v,hv⟩ := w.val.nonempty_supp
    have actual := factorCritical_order_rank w.val.toSimpleGraph (K.critical w.val).2 ⟨v,hv⟩
    change Nat.card w.val.supp=2*matchingEdges w.val.toSimpleGraph+1 at actual
    have bound := floor w mem
    change Z≤matchingEdges w.val.toSimpleGraph at bound
    omega
  obtain ⟨U,sub,ind,size⟩ := half_cap_piece_independent_supply G K.barrier outside p Z b positive num orders cap need
  have full : outside⊆{c|allFullComponent G K.barrier (2*p) c} := by
    rintro _ ⟨c,_,rfl⟩;exact K.full c.property.1
  refine ⟨U,size,ind,fun x mem => regionCore_full_degree G K.barrier outside (2*p) full (sub mem),?_⟩
  intro c hc x y edge hx
  obtain ⟨z,hz,rfl⟩ := ((wholePiece_adj G K.barrier c.val x y).mp edge).2.1
  obtain ⟨v,eq,w,mem,tag⟩ := sub hx
  have same : v=z := Subtype.ext eq
  subst v
  have label : (G.induce K.barrierᶜ).connectedComponentMk z=c.val := hz
  have equal : w=c := Subtype.ext (tag.trans label)
  exact (Finset.mem_compl.mp mem) (equal.symm ▸ hc)

#print axioms half_cap_spare_vertices
end JSP452Audit.StarHost
