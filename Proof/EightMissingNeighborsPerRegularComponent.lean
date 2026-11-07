import EightPenultimateArithmetic
namespace JSP452Audit.StarHost
open SimpleGraph

theorem eight_outside_each_independent_piece {X:Type*} [Finite X] (G:SimpleGraph X)
    (T:Finset G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents G 8)
    (A:Set (componentVertices G T)) (ind:(G.induce (componentVertices G T)).IsIndepSet A) :
    A.ncard+8*T.card≤(componentVertices G T).ncard := by
  classical
  let U := componentVertices G T
  let color (v:↥(Aᶜ:Set U)) : ↥T := ⟨G.connectedComponentMk v.val.val,v.val.property⟩
  have group (c:↥T) : 8≤Nat.card {v:↥(Aᶜ:Set U) // color v=c} := by
    let lift (v:c.val.supp) : U := ⟨v.val,by change G.connectedComponentMk v.val∈T;rw [show G.connectedComponentMk v.val=c.val from v.property];exact c.property⟩
    have reg (v:c.val.supp) := (component_degree_eq G c.val v).trans ((actual c.val c.property).2 v.val v.property)
    have pick : ∃v:c.val.supp,∀w:c.val.supp,c.val.toSimpleGraph.Adj v w → lift w∉A := by
      by_cases hit:∃v:c.val.supp,lift v∈A
      · obtain ⟨v,hv⟩ := hit
        exact ⟨v,fun w edge hw => ind hv hw (fun eq => edge.ne (Subtype.ext (congrArg (fun x:U => x.val) eq))) edge⟩
      · exact ⟨c.val.nonempty_supp.to_subtype.some,fun w _ hw => hit ⟨w,hw⟩⟩
    obtain ⟨v,away⟩ := pick
    let send (w:c.val.toSimpleGraph.neighborSet v) : {y:↥(Aᶜ:Set U) // color y=c} :=
      ⟨⟨lift w.val,away w.val w.property⟩,Subtype.ext w.val.property⟩
    have inj : Function.Injective send := fun _ _ eq => Subtype.ext (Subtype.ext (congrArg (fun y:{v:↥(Aᶜ:Set U) // color v=c} => y.val.val.val) eq))
    exact (reg v).symm.trans_le (Nat.card_le_card_of_injective send inj)
  have sum := Finset.sum_le_sum (s:=(Finset.univ:Finset ↥T)) (fun c _ => group c)
  have total := Nat.card_congr (Equiv.sigmaFiberEquiv color)
  rw [Nat.card_sigma] at total
  rw [total,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,Nat.cast_id] at sum
  change T.card*8≤Aᶜ.ncard at sum
  have order := Set.ncard_add_ncard_compl A
  change A.ncard+Aᶜ.ncard=(componentVertices G T).ncard at order
  omega

#print axioms eight_outside_each_independent_piece
end JSP452Audit.StarHost
