import TheActualPortEdgeGraphAllowsSeveralUsesOfALowDegreeRoot
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {D k c:ℕ} {K:DegreeRegion G D}

theorem join_when_one_valence_vanishes (U V:SimpleGraph X) (x:X) :
    (Nat.card (U.neighborSet x)=0 → Nat.card ((U⊔V).neighborSet x)=Nat.card (V.neighborSet x)) ∧
    (Nat.card (V.neighborSet x)=0 → Nat.card ((U⊔V).neighborSet x)=Nat.card (U.neighborSet x)) := by
  have merge (A B:SimpleGraph X) (zero:Nat.card (A.neighborSet x)=0) : (A⊔B).neighborSet x=B.neighborSet x := by
    ext y
    constructor
    · rintro (adj|adj)
      · have some : Nonempty (A.neighborSet x) := ⟨⟨y,adj⟩⟩
        have := Nat.card_pos (α:=A.neighborSet x);omega
      · exact adj
    · exact Or.inr
  exact ⟨fun zero => by rw [merge U V zero],fun zero => by rw [sup_comm U V,merge V U zero]⟩

namespace ScaledPortPlan
variable (P:ScaledPortPlan K k c)

theorem actual_layer_edge_subgraph (t:Fin k) :
    ∃(H:SimpleGraph X) (U:Set X),H≤G ∧
      (∀x∈U,x∉K.barrier ∧ Nat.card (G.neighborSet x)=D) ∧
      U.ncard=((P.layers.assigned t)ᶜ:Set K.pieces).ncard ∧
      (∀x∈K.barrier,Nat.card (H.neighborSet x)=P.degreeAt t x) ∧
      (∀x∉K.barrier,Nat.card (H.neighborSet x)≤1) ∧
      (∀x,Nat.card (G.neighborSet x)=D →
        (x∈U → Nat.card (H.neighborSet x)=0) ∧ (x∉U → Nat.card (H.neighborSet x)=1)) := by
  classical
  obtain ⟨pick,port,special⟩ := P.choose_layer_representatives t
  let label (Q:(G.induce K.barrierᶜ).ConnectedComponent) : X := (pick Q).val.val
  let p := P.parent t
  let z (i:P.portLabels t) := label (P.component t i)
  let H₀ := originalPortEdges G p z port
  have inject := picked_original_injective G K.barrier pick
  have iz : Function.Injective z := inject.comp (P.component_injective t)
  have root (i) : p i∈K.barrier := (P.port_incidence t i).1
  have out (i) : z i∉K.barrier := (pick (P.component t i)).val.property
  obtain ⟨atRoot,atPort,absent⟩ := original_port_valences G K.barrier p z port root out iz
  obtain ⟨M,hm,inside⟩ := internal_matching_away_from_picks G K.barrier (fun Q => (K.critical Q).2) pick
  have mem (x:X) : x∈M.verts ↔ x∉K.barrier ∧ x∉Set.range label := by
    constructor
    · intro hit;obtain ⟨Q,y,rfl,diff⟩ := (inside x).mp hit
      refine ⟨y.val.property,?_⟩
      rintro ⟨T,eq⟩
      have same : (pick T).val=y.val := Subtype.ext eq
      have matchQ : T=Q := ConnectedComponent.eq_of_common_vertex (pick T).property (same ▸ y.property)
      subst T;exact diff (Subtype.ext same.symm)
    · rintro ⟨out,none⟩
      let v:↥(K.barrierᶜ:Set X) := ⟨x,out⟩
      let Q := (G.induce K.barrierᶜ).connectedComponentMk v
      let y : Q.supp := ⟨v,rfl⟩
      exact (inside x).mpr ⟨Q,y,rfl,fun eq => none ⟨Q,congrArg (fun s:Q.supp => s.val.val) eq.symm⟩⟩
  let H := M.spanningCoe⊔H₀
  let free : Set (G.induce K.barrierᶜ).ConnectedComponent :=
    {Q|Q∉Set.range (P.component t) ∧ allFullComponent G K.barrier D Q}
  let U := label '' free
  have mat (x:X) : Nat.card (M.spanningCoe.neighborSet x)=(if x∈M.verts then 1 else 0) := matching_neighbor_indicator M hm x
  have on_root (x) (hx:x∈K.barrier) : Nat.card (H.neighborSet x)=P.degreeAt t x := by
    have no : x∉M.verts := fun m => ((mem x).1 m).1 hx
    have zero := mat x;rw [if_neg no] at zero
    exact ((join_when_one_valence_vanishes M.spanningCoe H₀ x).1 zero).trans (atRoot x hx)
  have isHole (Q) : label Q∈U ↔ Q∈free := by
    constructor
    · rintro ⟨T,f,eq⟩;exact inject eq ▸ f
    · exact fun f => ⟨Q,f,rfl⟩
  have atLabel (Q) : Nat.card (H.neighborSet (label Q))=if Q∈Set.range (P.component t) then 1 else 0 := by
    have no : label Q∉M.verts := fun m => ((mem _).mp m).2 ⟨Q,rfl⟩
    have zero := mat (label Q);rw [if_neg no] at zero
    rw [(join_when_one_valence_vanishes M.spanningCoe H₀ _).1 zero]
    by_cases named:Q∈Set.range (P.component t)
    · rw [if_pos named];obtain ⟨i,rfl⟩ := named;exact atPort i
    · rw [if_neg named]
      apply absent (label Q) (pick Q).val.property
      rintro ⟨i,eq⟩;exact named ⟨i,inject eq⟩
  have other (x) (out:x∉K.barrier) (nox:x∉Set.range label) : Nat.card (H.neighborSet x)=1 := by
    have no : x∉Set.range z := by rintro ⟨i,rfl⟩;exact nox ⟨P.component t i,rfl⟩
    have m := mat x;rw [if_pos ((mem x).2 ⟨out,nox⟩)] at m
    exact ((join_when_one_valence_vanishes M.spanningCoe H₀ x).2 (absent x out no)).trans m
  refine ⟨H,U,sup_le M.spanningCoe_le (original_ports_are_edges G p z port),?_,?_,on_root,?_,?_⟩
  · rintro _ ⟨Q,hQ,rfl⟩;exact ⟨(pick Q).val.property,hQ.2 (pick Q)⟩
  · change (label '' free).ncard=_
    rw [Set.ncard_image_of_injective _ inject]
    change ({Q|Q∉Set.range (P.component t) ∧ allFullComponent G K.barrier D Q}:Set _).ncard=_
    rw [P.free_full_cores_in_one_layer,Set.ncard_image_of_injective _ Subtype.val_injective]
  · intro x out
    by_cases used:x∈Set.range label
    · obtain ⟨Q,rfl⟩ := used;rw [atLabel];split <;> omega
    · exact (other x out used).le
  · intro x full
    by_cases root:x∈K.barrier
    · have no : x∉U := by rintro ⟨Q,_,rfl⟩;exact (pick Q).val.property root
      exact ⟨fun hit => (no hit).elim,fun _ => (on_root x root).trans ((P.layer_root_degrees t x root).2 full)⟩
    by_cases used:x∈Set.range label
    · obtain ⟨Q,rfl⟩ := used
      rw [atLabel,isHole]
      by_cases hit:Q∈Set.range (P.component t)
      · rw [if_pos hit];exact ⟨fun m => (m.1 hit).elim,fun _ => rfl⟩
      · have miss:Q∈free := ⟨hit,(special Q hit).1 full⟩
        rw [if_neg hit];exact ⟨fun _ => rfl,fun no => (no miss).elim⟩
    · have no : x∉U := by rintro ⟨Q,_,eq⟩;exact used ⟨Q,eq⟩
      exact ⟨fun hit => (no hit).elim,fun _ => other x root used⟩

#print axioms actual_layer_edge_subgraph
end ScaledPortPlan
#print axioms join_when_one_valence_vanishes
end JSP452Audit.StarHost
