import GeneralPairAuxiliaryDegree
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost.PairedLayers
open SimpleGraph
variable (k:ℕ)

def activePorts {X I:Type*} (t:I×Fin 2→X) (R:SimpleGraph (X⊕(I×Fin (2*(k+1)+1)))) (i:I) : Set (Fin 2) :=
  {j|R.Adj (.inr (portNode k i j)) (.inl (t (i,j)))}

theorem palette_cross_count_ports {X I:Type*} [Finite X] [Finite I] (Q:SimpleGraph X) (t:I×Fin 2→X)
    (R:SimpleGraph (X⊕(I×Fin (2*(k+1)+1)))) (sub:R≤pairedExtension k Q t) (i:I) :
    crossCount R (blockSet k i) (blockSet k i)ᶜ=(activePorts k t R i).ncard := by
  let S : Set (X⊕(I×Fin (2*(k+1)+1))) := blockSet k i
  let V := {p:↥S×↥(Sᶜ:Set (X⊕(I×Fin (2*(k+1)+1)))) // R.Adj p.1.val p.2.val}
  let send (j:↥(activePorts k t R i)) : V :=
    ⟨(⟨.inr (portNode k i j.val),(portEmbedding k) j.val,rfl⟩,
      ⟨.inl (t (i,j.val)),by rintro ⟨p,eq⟩;cases eq⟩),j.property⟩
  have inj : Function.Injective send := by
    intro a b eq
    have nodes := congrArg (fun e:V => e.val.1.val) eq
    have same : portNode k i a.val=portNode k i b.val := Sum.inr.inj nodes
    exact Subtype.ext ((portEmbedding k).injective (congrArg Prod.snd same))
  have onto : Function.Surjective send := by
    rintro ⟨⟨⟨x,mem⟩,⟨y,away⟩⟩,edge⟩
    obtain ⟨p,rfl⟩ := mem
    cases y with
    | inl v =>
      obtain ⟨j,hp,tip⟩ := (show hook k t v (i,p) from sub edge)
      change (portEmbedding k) j=p at hp
      change t (i,j)=v at tip
      subst p
      subst v
      exact ⟨⟨j,edge⟩,rfl⟩
    | inr z =>
      rcases z with ⟨k,q⟩
      have ik : i=k := (sub edge).1
      exact (away ⟨q,congrArg Sum.inr (congrArg (fun v => (v,q)) ik)⟩).elim
  exact (Nat.card_congr (Equiv.ofBijective send ⟨inj,onto⟩)).symm

theorem exact_layer_at_full_vertex {X:Type*} [Finite X] (H:SimpleGraph X)
    (V:TwoDegreeLayers H (k+1)) (x:X) (full:(H.neighborSet x).ncard=2*(k+1))
    (j:Fin (k+1)) : ((V.part j).neighborSet x).ncard=2 := by
  classical
  by_contra ne
  have less : ((V.part j).neighborSet x).ncard<2 := lt_of_le_of_ne (V.cap j x) ne
  have strict := Finset.sum_lt_sum (s:=Finset.univ) (g:=fun _ : Fin (k+1) => 2)
    (fun i _ => V.cap i x) ⟨j,Finset.mem_univ _,less⟩
  change (∑i:Fin (k+1),((V.part i).neighborSet x).ncard)<∑_:Fin (k+1),(2:ℕ) at strict
  rw [V.total,full,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at strict
  omega

theorem two_ports_same_layer {X I:Type*} [Finite X] [Finite I] (Q:SimpleGraph X) (t:I×Fin 2→X)
    (V:TwoDegreeLayers (pairedExtension k Q t) (k+1)) (j:Fin (k+1)) (i:I) :
    (0:Fin 2)∈activePorts k t (V.part j) i ↔ (1:Fin 2)∈activePorts k t (V.part j) i := by
  let S : Set (X⊕(I×Fin (2*(k+1)+1))) := blockSet k i
  let R := V.part j
  have full (v) (mem:v∈S) : Nat.card (R.neighborSet v)=2 := by
    obtain ⟨p,rfl⟩ := mem
    exact exact_layer_at_full_vertex k _ V _ (new_vertex_paired_extension_degree k Q t i p) j
  have hand := JSP452Audit.StarHost.two_block_handshake R S
  have degree := degree_sum_full R S 2 full
  have cross := palette_cross_count_ports k Q t R (V.sub j) i
  change crossCount R S Sᶜ=(activePorts k t R i).ncard at cross
  rw [degree,cross] at hand
  have notOne : (activePorts k t R i).ncard≠1 := by omega
  change (0:Fin 2)∈activePorts k t R i ↔ (1:Fin 2)∈activePorts k t R i
  constructor <;> intro yes <;> by_contra no
  · have singleton : activePorts k t R i={(0:Fin 2)} := by ext j;fin_cases j <;> simp [yes,no]
    exact notOne (singleton ▸ Set.ncard_singleton _)
  · have singleton : activePorts k t R i={(1:Fin 2)} := by ext j;fin_cases j <;> simp [yes,no]
    exact notOne (singleton ▸ Set.ncard_singleton _)

#print axioms palette_cross_count_ports
#print axioms exact_layer_at_full_vertex
#print axioms two_ports_same_layer
end JSP452Audit.StarHost.PairedLayers
