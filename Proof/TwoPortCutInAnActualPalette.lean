import FullAuxiliaryPortDegrees
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph

def activePorts {X I:Type*} (t:I×Fin 2→X) (R:SimpleGraph (X⊕(I×Fin 5))) (i:I) : Set (Fin 2) :=
  {j|R.Adj (.inr (portNode i j)) (.inl (t (i,j)))}

theorem palette_cross_count_ports {X I:Type*} [Finite X] [Finite I] (Q:SimpleGraph X) (t:I×Fin 2→X)
    (R:SimpleGraph (X⊕(I×Fin 5))) (sub:R≤pairedExtension Q t) (i:I) :
    crossCount R (blockSet i) (blockSet i)ᶜ=(activePorts t R i).ncard := by
  let S : Set (X⊕(I×Fin 5)) := blockSet i
  let V := {p:↥S×↥(Sᶜ:Set (X⊕(I×Fin 5))) // R.Adj p.1.val p.2.val}
  let send (j:↥(activePorts t R i)) : V :=
    ⟨(⟨.inr (portNode i j.val),portEmbedding j.val,rfl⟩,
      ⟨.inl (t (i,j.val)),by rintro ⟨p,eq⟩;cases eq⟩),j.property⟩
  have inj : Function.Injective send := by
    intro a b eq
    have nodes := congrArg (fun e:V => e.val.1.val) eq
    have same : portNode i a.val=portNode i b.val := Sum.inr.inj nodes
    exact Subtype.ext (portEmbedding.injective (congrArg Prod.snd same))
  have onto : Function.Surjective send := by
    rintro ⟨⟨⟨x,mem⟩,⟨y,away⟩⟩,edge⟩
    obtain ⟨p,rfl⟩ := mem
    cases y with
    | inl v =>
      obtain ⟨j,hp,tip⟩ := (show hook t v (i,p) from sub edge)
      change portEmbedding j=p at hp
      change t (i,j)=v at tip
      subst p
      subst v
      exact ⟨⟨j,edge⟩,rfl⟩
    | inr z =>
      rcases z with ⟨k,q⟩
      have ik : i=k := (sub edge).1
      exact (away ⟨q,congrArg Sum.inr (congrArg (fun v => (v,q)) ik)⟩).elim
  exact (Nat.card_congr (Equiv.ofBijective send ⟨inj,onto⟩)).symm

theorem palette_neighbor_sum {X:Type*} [Finite X] (H R:SimpleGraph X) (sub:R≤H) (v:X) :
    (R.neighborSet v).ncard+((H \ R).neighborSet v).ncard=(H.neighborSet v).ncard := by
  have dis : Disjoint (R.neighborSet v) ((H \ R).neighborSet v) := Set.disjoint_left.mpr (fun _ r b => b.2 r)
  have all : R.neighborSet v∪(H \ R).neighborSet v=H.neighborSet v := by
    ext w
    exact ⟨fun h => h.elim (fun e => sub e) (fun e => e.1),fun e =>
      by by_cases hit:R.Adj v w;exact Or.inl hit;exact Or.inr ⟨e,hit⟩⟩
  exact (Set.ncard_union_eq dis).symm.trans (congrArg Set.ncard all)

theorem two_ports_same_color {X I:Type*} [Finite X] [Finite I] (Q:SimpleGraph X) (t:I×Fin 2→X)
    (R:SimpleGraph (X⊕(I×Fin 5))) (sub:R≤pairedExtension Q t)
    (cap:∀v,Nat.card (R.neighborSet v)≤2 ∧ Nat.card (((pairedExtension Q t) \ R).neighborSet v)≤2) (i:I) :
    (0:Fin 2)∈activePorts t R i ↔ (1:Fin 2)∈activePorts t R i := by
  let S : Set (X⊕(I×Fin 5)) := blockSet i
  have full (v) (mem:v∈S) : Nat.card (R.neighborSet v)=2 := by
    obtain ⟨p,rfl⟩ := mem
    have four := new_vertex_paired_extension_degree Q t i p
    have both := cap (.inr (i,p))
    have sum := palette_neighbor_sum (pairedExtension Q t) R sub (.inr (i,p))
    change ((pairedExtension Q t).neighborSet (.inr (i,p))).ncard=4 at four
    change (R.neighborSet (.inr (i,p))).ncard≤2 ∧ (((pairedExtension Q t) \ R).neighborSet (.inr (i,p))).ncard≤2 at both
    change (R.neighborSet (.inr (i,p))).ncard=2
    omega
  have hand := JSP452Audit.StarHost.two_block_handshake R S
  have degree := degree_sum_full R S 2 full
  have cross := palette_cross_count_ports Q t R sub i
  change crossCount R S Sᶜ=(activePorts t R i).ncard at cross
  rw [degree,cross] at hand
  have notOne : (activePorts t R i).ncard≠1 := by omega
  constructor <;> intro yes <;> by_contra no
  · have singleton : activePorts t R i={(0:Fin 2)} := by ext j;fin_cases j <;> simp [yes,no]
    exact notOne (singleton ▸ Set.ncard_singleton _)
  · have singleton : activePorts t R i={(1:Fin 2)} := by ext j;fin_cases j <;> simp [yes,no]
    exact notOne (singleton ▸ Set.ncard_singleton _)

#print axioms palette_cross_count_ports
#print axioms palette_neighbor_sum
#print axioms two_ports_same_color
end JSP452Audit.StarHost
