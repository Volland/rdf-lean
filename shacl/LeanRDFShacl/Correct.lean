import LeanRDFShacl.Validate

/-!
# The validator is correct

`results_nil`: a focus node has no results exactly when it conforms. From it,
`validate_conforms`: the report conforms exactly when the data graph conforms to the shapes; and
`validate_sound`: every reported result names a shape and one of its components that fails at
the result's focus node.
-/

namespace LeanRDF.Shacl

open Vocab

variable (G : Graph)

/-! ## Value nodes, instances and counts -/

theorem mem_vals {path : Option Path} {x v : Term} : v ∈ vals G path x ↔ VN G path x v := by
  cases path with
  | none => simp [vals, VN]
  | some p => exact valueNodes_iff

theorem vals_nodup (path : Option Path) (x : Term) : (vals G path x).Nodup := by
  cases path with
  | none => exact List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
  | some p => exact valueNodes_nodup G p x

theorem pred_iff {p : IRI} {x y : Term} : ValueNode G (.pred p) x y ↔ ⟨x, .iri p, y⟩ ∈ G :=
  ⟨fun h => by cases h with | pred h => exact h, .pred⟩

theorem mem_pred {p : IRI} {x y : Term} : y ∈ valueNodes G (.pred p) x ↔ ⟨x, .iri p, y⟩ ∈ G :=
  valueNodes_iff.trans (pred_iff G)

theorem instB_iff {v c : Term} : instB G v c = true ↔ InstanceOf G v c := by
  simp only [instB, List.any_eq_true, List.contains_iff_mem, valueNodes_iff, pred_iff, InstanceOf]

/-- The values that pass a filter, reported one by one, are none exactly when every value node
passes. -/
theorem filter_vals {β : Type} {path : Option Path} {x : Term} {f : Term → Bool} {g : Term → β}
    {P : Term → Prop} (h : ∀ v, f v = false ↔ P v) :
    ((vals G path x).filter f).map g = [] ↔ ∀ v, VN G path x v → P v := by
  simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff, Bool.not_eq_true]
  exact ⟨fun h' v hv => (h v).1 (h' v ((mem_vals G).2 hv)),
    fun h' v hv => (h v).2 (h' v ((mem_vals G).1 hv))⟩

/-- A list without duplicates that lists `P` counts it: at least `n`. -/
theorem count_ge {l : List Term} {P : Term → Prop} (hl : l.Nodup) (hP : ∀ y, y ∈ l ↔ P y)
    (n : Nat) : n ≤ l.length ↔ ∃ m : List Term, m.Nodup ∧ (∀ y ∈ m, P y) ∧ n ≤ m.length :=
  ⟨fun h => ⟨l, hl, fun y hy => (hP y).1 hy, h⟩, fun ⟨m, hm, hmP, hn⟩ =>
    Nat.le_trans hn (List.Nodup.length_le_of_subset hm fun y hy => (hP y).2 (hmP y hy))⟩

/-- … and at most `n`. -/
theorem count_le {l : List Term} {P : Term → Prop} (hl : l.Nodup) (hP : ∀ y, y ∈ l ↔ P y)
    (n : Nat) : l.length ≤ n ↔ ∀ m : List Term, m.Nodup → (∀ y ∈ m, P y) → m.length ≤ n :=
  ⟨fun h m hm hmP => Nat.le_trans (List.Nodup.length_le_of_subset hm fun y hy => (hP y).2 (hmP y hy)) h,
    fun h => h l hl fun y hy => (hP y).1 hy⟩

theorem dupLangs_nil {vs : List Term} :
    dupLangs vs = [] ↔ ∀ y ∈ vs, ∀ z ∈ vs, y ≠ z → langOf y = none ∨ langOf y ≠ langOf z := by
  rw [List.eq_nil_iff_forall_not_mem]
  simp only [dupLangs, mem_uniq, List.mem_filterMap]
  constructor
  · intro h y hy z hz hne
    cases hl : langOf y with
    | none => exact .inl rfl
    | some t =>
      refine .inr fun heq => h t ⟨y, hy, ?_⟩
      have hany : (vs.any fun z => z != y && langOf z == some t) = true :=
        List.any_eq_true.2 ⟨z, hz, by
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
          exact ⟨Ne.symm hne, heq.symm⟩⟩
      simp only [hl, hany, ↓reduceIte]
  · rintro h t ⟨y, hy, hf⟩
    cases hl : langOf y with
    | none => rw [hl] at hf; cases hf
    | some t' =>
      simp only [hl] at hf
      by_cases hany : (vs.any fun z => z != y && langOf z == some t') = true
      · obtain ⟨z, hz, hzz⟩ := List.any_eq_true.1 hany
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hzz
        rcases h y hy z hz (Ne.symm hzz.1) with h' | h'
        · rw [hl] at h'; cases h'
        · exact h' (hl.trans hzz.2.symm)
      · simp [hany] at hf

theorem allowedB_iff {allowed : List IRI} {p : Term} :
    allowedB allowed p = true ↔ ∃ q ∈ allowed, p = .iri q := by
  cases p with
  | iri q => simp [allowedB]
  | bnode b => simp [allowedB]
  | lit l => simp [allowedB]
  | triple s p o => simp [allowedB]

theorem if_nil {c : Prop} [Decidable c] {r : Result} : (if c then [r] else []) = [] ↔ ¬ c := by
  by_cases h : c <;> simp [h]

/-! ## No results exactly when the node conforms -/

mutual
theorem results_nil : ∀ (s : Shape) (x : Term), results G s x = [] ↔ Conforms G s x
  | .mk id path tg comps deact sev msgs, x => by
    rw [results, Conforms]
    cases deact
    · simp only [Bool.false_eq_true, ↓reduceIte, false_or]
      exact compsResults_nil ⟨id, path, sev, msgs⟩ comps x
    · simp
theorem compsResults_nil (k : Ctx) : ∀ (cs : List Component) (x : Term),
    compsResults G k cs x = [] ↔ CompsHold G k.path cs x
  | [], x => by simp [compsResults, CompsHold]
  | c :: cs, x => by
    rw [compsResults, CompsHold, List.append_eq_nil_iff, compResults_nil k c x, compsResults_nil k cs x]
theorem compResults_nil (k : Ctx) : ∀ (c : Component) (x : Term),
    compResults G k c x = [] ↔ CompHolds G k.path c x
  | .test t, x => by
    rw [compResults, CompHolds]; exact filter_vals G fun v => by simp
  | .class_ c, x => by
    rw [compResults, CompHolds]; exact filter_vals G fun v => by simp [instB_iff]
  | .minCount n, x => by
    rw [compResults, CompHolds, if_nil, Nat.not_lt,
      count_ge (vals_nodup G _ _) (fun y => mem_vals G)]
  | .maxCount n, x => by
    rw [compResults, CompHolds, if_nil, Nat.not_lt,
      count_le (vals_nodup G _ _) (fun y => mem_vals G)]
  | .uniqueLang, x => by
    rw [compResults, CompHolds, List.map_eq_nil_iff, dupLangs_nil]
    exact ⟨fun h y z hy hz => h y ((mem_vals G).2 hy) z ((mem_vals G).2 hz),
      fun h y hy z hz => h y z ((mem_vals G).1 hy) ((mem_vals G).1 hz)⟩
  | .equals p, x => by
    simp only [compResults, CompHolds, List.map_eq_nil_iff, List.append_eq_nil_iff,
      List.filter_eq_nil_iff, Bool.not_eq_true, Bool.not_eq_false', List.contains_iff_mem, mem_pred]
    constructor
    · rintro ⟨h1, h2⟩ v
      exact ⟨fun hv => h1 v ((mem_vals G).2 hv), fun hv => (mem_vals G).1 (h2 v hv)⟩
    · intro h
      exact ⟨fun v hv => (h v).1 ((mem_vals G).1 hv), fun v hv => (mem_vals G).2 ((h v).2 hv)⟩
  | .disjoint p, x => by
    rw [compResults, CompHolds]; exact filter_vals G fun v => by simp
  | .lessThan p, x => by
    simp only [compResults, CompHolds, List.map_eq_nil_iff, List.flatMap_eq_nil_iff,
      List.filter_eq_nil_iff, Bool.not_eq_true, Bool.not_eq_false', mem_pred]
    exact ⟨fun h v w hv hw => h v ((mem_vals G).2 hv) w hw,
      fun h v hv w hw => h v w ((mem_vals G).1 hv) hw⟩
  | .lessThanOrEquals p, x => by
    simp only [compResults, CompHolds, List.map_eq_nil_iff, List.flatMap_eq_nil_iff,
      List.filter_eq_nil_iff, Bool.not_eq_true, Bool.not_eq_false', mem_pred]
    exact ⟨fun h v w hv hw => h v ((mem_vals G).2 hv) w hw,
      fun h v hv w hw => h v w ((mem_vals G).1 hv) hw⟩
  | .not s, x => by
    rw [compResults, CompHolds]
    exact filter_vals G fun v => by
      rw [← Bool.not_eq_true, List.isEmpty_iff, results_nil s v]
  | .and ss, x => by
    rw [compResults, CompHolds]
    exact filter_vals G fun v => by rw [Bool.not_eq_false', allOk_iff ss v]
  | .or ss, x => by
    rw [compResults, CompHolds]
    exact filter_vals G fun v => by rw [Bool.not_eq_false', someOk_iff ss v]
  | .xone ss, x => by
    rw [compResults, CompHolds]
    exact filter_vals G fun v => by rw [Bool.not_eq_false', oneOk_iff ss v]
  | .node s, x => by
    rw [compResults, CompHolds]
    exact filter_vals G fun v => by rw [Bool.not_eq_false', List.isEmpty_iff, results_nil s v]
  | .property s, x => by
    rw [compResults, CompHolds, List.flatMap_eq_nil_iff]
    exact ⟨fun h v hv => (results_nil s v).1 (h v ((mem_vals G).2 hv)),
      fun h v hv => (results_nil s v).2 (h v ((mem_vals G).1 hv))⟩
  | .qualifiedMin s n sibs, x => by
    rw [compResults, CompHolds, if_nil, Nat.not_lt]
    refine count_ge ((vals_nodup G _ _).sublist List.filter_sublist) (fun y => ?_) n
    rw [List.mem_filter, mem_vals G, Bool.and_eq_true, List.isEmpty_iff, results_nil s y,
      noneOk_iff sibs y]
  | .qualifiedMax s n sibs, x => by
    rw [compResults, CompHolds, if_nil, Nat.not_lt]
    refine count_le ((vals_nodup G _ _).sublist List.filter_sublist) (fun y => ?_) n
    rw [List.mem_filter, mem_vals G, Bool.and_eq_true, List.isEmpty_iff, results_nil s y,
      noneOk_iff sibs y]
  | .closed allowed, x => by
    simp only [compResults, CompHolds, List.flatMap_eq_nil_iff, List.map_eq_nil_iff,
      List.filter_eq_nil_iff, Graph.mem_toList, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
      not_and, Bool.not_eq_false]
    constructor
    · intro h v hv p o ht
      have := h v ((mem_vals G).2 hv) ⟨v, p, o⟩ ht rfl
      exact allowedB_iff.1 (by simpa using this)
    · intro h v hv t ht hs
      obtain ⟨s', p, o⟩ := t
      simp only at hs; subst hs
      have := allowedB_iff.2 (h _ ((mem_vals G).1 hv) p o ht)
      simpa using this
  | .hasValue t, x => by
    rw [compResults, CompHolds]
    by_cases h : (vals G k.path x).contains t = true
    · simp only [h, ↓reduceIte]
      exact iff_of_true trivial ((mem_vals G).1 (List.contains_iff_mem.1 h))
    · have h' : (vals G k.path x).contains t = false := by simpa using h
      simp only [h', Bool.false_eq_true, ↓reduceIte]
      exact iff_of_false (by simp) fun hv => h (List.contains_iff_mem.2 ((mem_vals G).2 hv))
theorem allOk_iff : ∀ (ss : List Shape) (v : Term), allOk G ss v = true ↔ AllConform G ss v
  | [], v => by simp [allOk, AllConform]
  | s :: ss, v => by
    rw [allOk, AllConform, Bool.and_eq_true, List.isEmpty_iff, results_nil s v, allOk_iff ss v]
theorem someOk_iff : ∀ (ss : List Shape) (v : Term), someOk G ss v = true ↔ SomeConforms G ss v
  | [], v => by simp [someOk, SomeConforms]
  | s :: ss, v => by
    rw [someOk, SomeConforms, Bool.or_eq_true, List.isEmpty_iff, results_nil s v, someOk_iff ss v]
theorem noneOk_iff : ∀ (ss : List Shape) (v : Term), noneOk G ss v = true ↔ NoneConform G ss v
  | [], v => by simp [noneOk, NoneConform]
  | s :: ss, v => by
    rw [noneOk, NoneConform, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
      List.isEmpty_iff, results_nil s v, noneOk_iff ss v]
theorem oneOk_iff : ∀ (ss : List Shape) (v : Term), oneOk G ss v = true ↔ OneConforms G ss v
  | [], v => by simp [oneOk, OneConforms]
  | s :: ss, v => by
    rw [oneOk, OneConforms, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      ← Bool.not_eq_true, List.isEmpty_iff, results_nil s v, noneOk_iff ss v, oneOk_iff ss v]
end

/-! ## The report -/

theorem mem_targetNodes {tg : Target} {x : Term} : x ∈ targetNodes G tg ↔ TargetHolds G tg x := by
  cases tg with
  | node t => simp [targetNodes, TargetHolds]
  | class_ c =>
    simp only [targetNodes, TargetHolds, List.mem_map, List.mem_filter, Graph.mem_toList,
      Bool.and_eq_true, beq_iff_eq, instB_iff]
    constructor
    · rintro ⟨t, ⟨-, -, h⟩, rfl⟩; exact h
    · intro h
      obtain ⟨t, ht, ht'⟩ := id h
      exact ⟨_, ⟨ht, rfl, h⟩, rfl⟩
  | subjectsOf p =>
    simp only [targetNodes, TargetHolds, List.mem_map, List.mem_filter, Graph.mem_toList, beq_iff_eq]
    constructor
    · rintro ⟨⟨s, p', o⟩, ⟨ht, hp⟩, rfl⟩; simp only at hp; subst hp; exact ⟨o, ht⟩
    · rintro ⟨o, ht⟩; exact ⟨_, ⟨ht, rfl⟩, rfl⟩
  | objectsOf p =>
    simp only [targetNodes, TargetHolds, List.mem_map, List.mem_filter, Graph.mem_toList, beq_iff_eq]
    constructor
    · rintro ⟨⟨s, p', o⟩, ⟨ht, hp⟩, rfl⟩; simp only at hp; subst hp; exact ⟨s, ht⟩
    · rintro ⟨s, ht⟩; exact ⟨_, ⟨ht, rfl⟩, rfl⟩

theorem mem_focusNodes {s : Shape} {x : Term} : x ∈ focusNodes G s ↔ IsFocus G s x := by
  simp only [focusNodes, mem_uniq, List.mem_flatMap, mem_targetNodes, IsFocus]

-- @tg: implements:: [[openspec:shacl-core#Proven validator]] {note: "validate_conforms"}
/-- The report conforms exactly when the data graph conforms to the shapes. -/
theorem validate_conforms (S : List Shape) : (validate G S).conforms = true ↔ DataConforms G S := by
  simp only [validate, List.isEmpty_iff, List.flatMap_eq_nil_iff, DataConforms]
  exact ⟨fun h s hs x hx => (results_nil G s x).1 (h s hs x ((mem_focusNodes G).2 hx)),
    fun h s hs x hx => (results_nil G s x).2 (h s hs x ((mem_focusNodes G).1 hx))⟩

/-- A result is a real violation: some shape has a component, the result's, that fails at the
result's focus node. -/
def Violation (r : Result) : Prop :=
  ∃ s : Shape, s.id = r.source ∧ ∃ c ∈ s.comps, c.iri = r.component ∧ ¬ CompHolds G s.path c r.focus

/-- A component's own results name the shape, the component and the focus node. -/
theorem compResults_own {k : Ctx} {c : Component} {x : Term} {r : Result}
    (hnp : ∀ s, c ≠ .property s) (h : r ∈ compResults G k c x) :
    r.source = k.id ∧ r.component = c.iri ∧ r.focus = x := by
  cases c <;> simp only [compResults] at h
  all_goals first
    | exact absurd rfl (hnp _)
    | (obtain ⟨_, _, rfl⟩ := List.mem_map.1 h; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := List.mem_flatMap.1 h
       obtain ⟨_, _, rfl⟩ := List.mem_map.1 h; exact ⟨rfl, rfl, rfl⟩)
    | (split at h
       · rw [List.mem_singleton] at h; subst h; exact ⟨rfl, rfl, rfl⟩
       · exact absurd h List.not_mem_nil)
    | (split at h
       · exact absurd h List.not_mem_nil
       · rw [List.mem_singleton] at h; subst h; exact ⟨rfl, rfl, rfl⟩)

private theorem own {k : Ctx} {P : Shape} {c : Component} {x : Term} {r : Result}
    (hid : P.id = k.id) (hpath : P.path = k.path) (hc : c ∈ P.comps) (hnp : ∀ s, c ≠ .property s)
    (h : r ∈ compResults G k c x) : Violation G r := by
  obtain ⟨h1, h2, h3⟩ := compResults_own G hnp h
  refine ⟨P, hid.trans h1.symm, c, hc, h2.symm, ?_⟩
  rw [hpath, h3]
  intro hh
  rw [(compResults_nil G k c x).2 hh] at h
  exact absurd h List.not_mem_nil

mutual
theorem results_sound : ∀ (s : Shape) (x : Term) (r : Result), r ∈ results G s x → Violation G r
  | .mk id path tg comps deact sev msgs, x, r, h => by
    rw [results] at h
    split at h
    · exact absurd h List.not_mem_nil
    · exact compsResults_sound ⟨id, path, sev, msgs⟩ (.mk id path tg comps deact sev msgs) rfl rfl
        comps (fun _ hc => hc) x r h
theorem compsResults_sound (k : Ctx) (P : Shape) (hid : P.id = k.id) (hpath : P.path = k.path) :
    ∀ (cs : List Component), (∀ c ∈ cs, c ∈ P.comps) → ∀ (x : Term) (r : Result),
      r ∈ compsResults G k cs x → Violation G r
  | [], _, _, _, h => absurd h List.not_mem_nil
  | c :: cs, hcs, x, r, h => by
    rw [compsResults, List.mem_append] at h
    rcases h with h | h
    · exact compResults_sound k P hid hpath c (hcs c List.mem_cons_self) x r h
    · exact compsResults_sound k P hid hpath cs (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) x r h
theorem compResults_sound (k : Ctx) (P : Shape) (hid : P.id = k.id) (hpath : P.path = k.path) :
    ∀ (c : Component), c ∈ P.comps → ∀ (x : Term) (r : Result),
      r ∈ compResults G k c x → Violation G r
  | .property s, _, x, r, h => by
    rw [compResults] at h
    obtain ⟨v, -, hv⟩ := List.mem_flatMap.1 h
    exact results_sound s v r hv
  | .test _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .class_ _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .minCount _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .maxCount _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .uniqueLang, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .equals _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .disjoint _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .lessThan _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .lessThanOrEquals _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .not _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .and _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .or _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .xone _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .node _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .qualifiedMin .., hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .qualifiedMax .., hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .closed _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
  | .hasValue _, hc, _, _, h => own G hid hpath hc (fun _ e => by cases e) h
end

-- @tg: implements:: [[openspec:shacl-core#Proven validator]] {note: "validate_sound"}
/-- Every result of the report is a real violation. -/
theorem validate_sound (S : List Shape) {r : Result} (h : r ∈ (validate G S).results) :
    Violation G r := by
  simp only [validate, List.mem_flatMap] at h
  obtain ⟨s, -, x, -, hr⟩ := h
  exact results_sound G s x r hr

end LeanRDF.Shacl
