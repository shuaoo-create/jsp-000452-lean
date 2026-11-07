import StrictSixLowColumnTaxes
namespace JSP452Audit.StarHost
open SimpleGraph

noncomputable def chosenSlots {X:Type*} [Finite X] (G:SimpleGraph X) (T:Finset G.ConnectedComponent) (x:ℕ) : ℕ :=
  ∑c∈T,Nat.card c.supp/(x+1)

theorem selected_component_pack {X:Type*} [Finite X] (G:SimpleGraph X) (T:Finset G.ConnectedComponent)
    (x:ℕ) (pos:0<x) : UniformPackCap (G.induce (componentVertices G T)) x (chosenSlots G T x) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have bot : G.induce (componentVertices G ∅)=⊥ := by ext v;exact (Finset.notMem_empty _ v.property).elim
    rw [bot]
    simpa [chosenSlots] using uniform_pack_bot_cap (X:=↥(componentVertices G ∅)) x pos
  | @insert c T fresh ih =>
    let V := componentVertices G T
    let U := componentVertices G (insert c T)
    have cover : c.supp∪V=U := by ext v;exact Finset.mem_insert.symm
    have apart : Disjoint c.supp V := Set.disjoint_left.mpr fun _ hc hv =>
      fresh ((show G.connectedComponentMk _=c from hc) ▸ hv)
    have sep (v:X) (hc:v∈c.supp) (w:X) (hw:w∈V) : ¬G.Adj v w := fun edge =>
      Set.disjoint_left.mp apart ((c.mem_supp_congr_adj edge).mp hc) hw
    let e := regionSumIso G U c.supp V cover apart sep
    intro k copy
    obtain ⟨f⟩ := copy
    obtain ⟨a,b,sum,left,right⟩ := uniform_copy_split_sum c.toSimpleGraph (G.induce V) x k ⟨e.symm.toCopy.comp f⟩
    have first := uniform_pack_order_cap c.toSimpleGraph x pos Set.univ (fun _ _ _ => Set.mem_univ _) a left
    rw [Set.ncard_univ] at first
    change a≤Nat.card c.supp/(x+1) at first
    have second := ih b right
    change k≤(∑i∈insert c T,Nat.card i.supp/(x+1))
    rw [Finset.sum_insert fresh]
    change b≤(∑i∈T,Nat.card i.supp/(x+1)) at second
    omega

theorem selected_subgraph_pack {X:Type*} [Finite X] (G:SimpleGraph X) (T:Finset G.ConnectedComponent)
    (P:SimpleGraph (componentVertices G T)) (sub:P≤G.induce (componentVertices G T)) (x:ℕ) (pos:0<x) :
    UniformPackCap P x (chosenSlots G T x) := fun k copy => selected_component_pack G T x pos k (copy.mono_right sub)

theorem uniform_pack_below_degree {X:Type*} [Finite X] (G:SimpleGraph X) (x:ℕ)
    (cap:∀v,Nat.card (G.neighborSet v)<x) : UniformPackCap G x 0 := by
  intro k copy
  by_contra! positive
  have bound := copied_head_degree_cap G (fun _:Fin k => x) copy (x-1) (fun v => by have := cap v;omega)
  have impossible := bound ⟨0,positive⟩
  have pos : 0<x := by
    obtain ⟨f⟩ := copy
    have := cap (f (center (fun _:Fin k => x) ⟨0,positive⟩));omega
  omega

#print axioms selected_component_pack
#print axioms selected_subgraph_pack
#print axioms uniform_pack_below_degree
end JSP452Audit.StarHost
