import TheActualBarrierPortsHaveThePromisedDegreesAcrossEveryLayer
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {D k c:ℕ} {K:DegreeRegion G D}
namespace ScaledPortPlan
variable (P:ScaledPortPlan K k c)

theorem choose_layer_representatives (t:Fin k) :
    ∃pick:∀Q:(G.induce K.barrierᶜ).ConnectedComponent,Q.supp,
      (∀i:P.portLabels t,G.Adj (P.parent t i) (pick (P.component t i)).val.val) ∧
      (∀Q,Q∉Set.range (P.component t) →
        (Nat.card (G.neighborSet (pick Q).val.val)=D ↔ allFullComponent G K.barrier D Q)) := by
  classical
  have chooseOne (Q:(G.induce K.barrierᶜ).ConnectedComponent) :
      ∃x:Q.supp,(∀i,P.component t i=Q → G.Adj (P.parent t i) x.val.val) ∧
        (Q∉Set.range (P.component t) → (Nat.card (G.neighborSet x.val.val)=D ↔ allFullComponent G K.barrier D Q)) := by
    by_cases used:Q∈Set.range (P.component t)
    · obtain ⟨i,rfl⟩ := used
      obtain ⟨_,x,edge⟩ := P.port_incidence t i
      exact ⟨x,fun j eq => (P.component_injective t eq) ▸ edge,fun no => (no ⟨i,rfl⟩).elim⟩
    · have never (i) (eq:P.component t i=Q) : False := used ⟨i,eq⟩
      by_cases full:allFullComponent G K.barrier D Q
      · let x := Classical.choice Q.nonempty_supp.to_subtype
        exact ⟨x,fun i eq => (never i eq).elim,fun _ => ⟨fun _ => full,fun h => h x⟩⟩
      · change ¬∀x:Q.supp,Nat.card (G.neighborSet x.val.val)=D at full
        obtain ⟨x,low⟩ := Classical.not_forall.mp full
        exact ⟨x,fun i eq => (never i eq).elim,fun _ => ⟨fun h => (low h).elim,fun h => h x⟩⟩
  exact ⟨fun Q => (chooseOne Q).choose,fun i => (chooseOne _).choose_spec.1 i rfl,
    fun Q => (chooseOne Q).choose_spec.2⟩

#print axioms choose_layer_representatives
end ScaledPortPlan
end JSP452Audit.StarHost
