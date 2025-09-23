section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro P
  intro notP
  apply notP P


theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro nP

  by_cases lem: P
  case pos =>
    assumption

  case neg =>
    contradiction


theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  constructor
  case mp =>
    intro nP

    by_cases lem: P
    case pos =>
      assumption

    case neg =>
      contradiction

  case mpr =>
    intro P
    intro notP
    apply notP P


------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro hpq
  cases hpq with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq


theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro hpq
  cases hpq with
  | intro hp hq =>
    exact ⟨hq, hp⟩

------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro npq
  intro p
  cases npq with
  | inl np =>
    contradiction

  | inr hq =>
    exact hq


theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro hpouq
  intro np
  cases hpouq with
  | inl np =>
    contradiction

  | inr hq =>
    exact hq


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro hptoq
  intro nq
  intro p
  have hq : Q := hptoq p
  apply nq hq


theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro nqtonp
  intro hp

  by_cases lemQ: Q
  case pos =>
    assumption

  case neg =>
    by_cases lemP: P
    case pos =>
      have hnP: ¬P := nqtonp lemQ
      contradiction

    case neg =>
      contradiction



theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor
  case mp =>
    intro hptoq
    intro nq
    intro p
    have hq : Q := hptoq p
    contradiction

  case mpr =>
    intro nqtonp
    intro hp

    by_cases lemQ: Q
    case pos =>
      assumption

    case neg =>
      by_cases lemP: P
      case pos =>
        have hnP: ¬P := nqtonp lemQ
        contradiction

      case neg =>
        contradiction



------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by

  intro hdenypornotp
  apply hdenypornotp

  by_cases lem : P
  case pos =>
    left
    exact lem

  case neg =>
    right
    exact lem



------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro ptoqtop


  by_cases lem : P
  case pos =>
    intro notp
    contradiction

  case neg =>
    intro notp
    apply notp
    apply ptoqtop
    intro p
    contradiction
    --Aqui é dificil explicar oque ocorre
    --apply muda o alvo, pq meio q o alvo antes de ptoqtop  bate com o alvo atual
    --assim eu introduzo p e como tenho o not p, contradição é trivial


------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
  by_cases lemP: P
  case pos =>
    right
    intro hQ
    trivial

  case neg =>
    left
    intro hP
    contradiction



------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro porq
  intro denyNotPorNotQ
  cases denyNotPorNotQ with
  | intro notP notQ =>
    cases porq with
    | inl hp =>
      contradiction

    | inr hq =>
      contradiction

theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro hpq
  cases hpq with
  | intro hp hq =>
    intro denyNotPorNotQ
    cases denyNotPorNotQ with
    | inl notP =>
      contradiction

    | inr notQ =>
      contradiction

------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro denyPorQ

  constructor
  case left =>
    intro hp
    apply denyPorQ
    left
    exact hp

  case right =>
    intro hq
    apply denyPorQ
    right
    exact hq


theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro notPorNotQ
  cases notPorNotQ with
    | intro notP notQ =>
      intro porq
      cases porq with
        | inl hp =>
          contradiction

        | inr hq =>
          contradiction


theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  intro denyPQ
  by_cases lemP: P
  case pos =>

    by_cases lemQ: Q
    case pos =>
      right
      intro hP
      apply denyPQ
      exact ⟨lemP, lemQ⟩

    case neg =>
      left
      exact lemQ

  case neg =>

    right
    exact lemP


theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  intro notQorNotP
  intro PandQ
  cases PandQ with
  | intro hp hq =>
    cases notQorNotP with
    | inl hnotQ =>
      contradiction

    | inr hnotP =>
      contradiction


theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  constructor
  case mp =>
    intro denyPQ
    by_cases lemP: P
    case pos =>

      by_cases lemQ: Q
      case pos =>
        right
        intro hP
        apply denyPQ
        exact ⟨lemP, lemQ⟩

      case neg =>
        left
        exact lemQ

    case neg =>

      right
      exact lemP

  case mpr =>
    intro notQNotP
    cases notQNotP with
    | inl notQ =>
      intro PQ
      cases PQ with
      | intro hp hq =>
        contradiction


    | inr notP =>
      intro PQ
      cases PQ with
      | intro hp hq =>
        contradiction


theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by

  constructor
  case mp =>
    intro denyPQ

    constructor
    case left =>
      intro p
      apply denyPQ
      left
      exact p

    case right =>
      intro q
      apply denyPQ
      right
      exact q


  case mpr =>
    intro NotPNotQ
    intro PorQ
    cases NotPNotQ with
    | intro notP notQ =>
      cases PorQ with
      | inl p =>
        apply notP p

      | inr q =>
        apply notQ q



------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  intro PQorR

  cases PQorR with
  | intro hP QorR =>
    cases QorR with
    | inl hQ =>
      left
      exact ⟨hP, hQ⟩

    | inr hR =>
      right
      exact ⟨hP, hR⟩


theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  intro hPQorPR
  cases hPQorPR with
  | inl hPQ =>
    cases hPQ with
    | intro hP hQ =>
      constructor
      case left =>
        exact hP
      case right =>
        left
        exact hQ

  | inr hPR =>
    cases hPR with
    | intro hP hR =>
      constructor
      case left =>
        exact hP

      case right =>
        right
        exact hR


theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  intro hPorQR

  constructor
  case left =>
    cases hPorQR with
    | inl hP =>
      left
      exact hP
    | inr hQR =>
      right
      cases hQR with
      | intro hQ hR =>
        exact hQ
  case right =>
    cases hPorQR with
    | inl hP =>
      left
      exact hP
    | inr hQR =>
      right
      cases hQR with
      | intro hQ hR =>
        exact hR

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by

  intro PorQPorR
  cases PorQPorR with
  | intro hPorQ hPorR =>
    cases hPorQ with
    | inl hP =>
      left
      exact hP

    | inr hQ =>
      cases hPorR with
      | inl hP =>
        left
        assumption

      | inr hR =>
        right
        exact ⟨hQ, hR⟩


------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro hPQtoR
  intro hp
  intro hq
  apply hPQtoR
  trivial

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro hPtoQtoR
  intro hPQ
  cases hPQ with
  | intro hP hQ =>
    apply hPtoQtoR hP hQ



------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro hP
  trivial


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  intro hP
  left
  trivial

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  intro hQ
  right
  trivial

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  intro hPQ
  exact hPQ.left


theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  intro hPQ
  exact hPQ.right

------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  constructor
  case mp =>
    intro hPorP
    cases hPorP with
    | inl hP =>
      trivial

    | inr hP2 =>
      trivial

  case mpr =>
    intro hP
    left
    trivial

theorem conj_idem :
  (P ∧ P) ↔ P := by
  constructor
  case mp =>
    intro hPP
    exact hPP.left

  case mpr =>
    intro hP
    exact ⟨hP, hP⟩



------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  intro no
  contradiction

theorem true_top :
  P → True  := by
  intro hP
  trivial

end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Prop)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  intro hdenyExPx
  intro hx
  intro hU

  have hPx : (∃ x, P x) := by
    apply Exists.intro hx hU

  contradiction


theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by


theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  sorry

theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
