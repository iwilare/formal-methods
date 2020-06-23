open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function.Equivalence using (_⇔_; equivalence; Equivalence)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import IMP
open import OperationalSemantics
open import Hoare

wp : ∀ {l} → com → assn {l} → assn {l}
wp c Q s = ∀ t → ⦅ c , s ⦆⇒ t → Q t

{-
wp1 : ∀ {l} → com {l} → assn l → assn l
wp1 SKIP Q = Q
wp1 (x ::= a) Q s = Q (s [ x ::= aval a s ])
wp1 (c₁ :: c₂) Q = wp c₁ (wp c₂ Q)
wp1 (IF b THEN c₁ ELSE c₂) Q s with bval b s
... | true = wp c₁ Q s
... | false = wp c₂ Q s
wp1 (WHILE b DO c) Q s with bval b s
... | true = wp1 (c :: (WHILE b DO c)) Q s
... | false = Q s
-}

fatto : ∀ {P Q : assn} {c}
       → ⊨[ P ] c [ Q ]
       → (∀ s → P s → wp c Q s)
fatto = λ z s z₁ t → z z₁

fatto-converse : ∀ {P Q : assn} {c}
      → (∀ s → P s → wp c Q s)
      → ⊨[ P ] c [ Q ]
fatto-converse = (λ z {s} {t} z₁ → z s z₁ t)

{-
postulate
  eq-wp1 : ∀ {l}{Q : assn l}{x a}
         → wp (x ::= a) Q ≡ λ s → Q (s [ x ::= aval a s ])

wp-hoare : ∀ {l} {Q : assn l} (c)
      → ⊢[ wp c Q ] c [ Q ]
wp-hoare SKIP = Conseq (λ s z → z s Skip) (λ s z → z) Skip
wp-hoare {l}{Q} (x ::= a) rewrite eq-wp1 {l}{Q}{x}{a} = Loc
wp-hoare (c :: c₁) = Comp (Conseq (λ s z x x₁ x₂ x₃ → z x₂ (Comp x₁ x₃)) (λ s z → z) (wp-hoare c)) (wp-hoare c₁)
wp-hoare (IF x THEN c ELSE c₁) = {!!}
wp-hoare (WHILE x DO c) = {!!}      
-}

postulate
   wp-hoare : ∀ {l} {Q : assn {l}} (c)
      → ⊢[ wp c Q ] c [ Q ]

completeness : ∀ {P Q : assn} (c)
  → ⊨[ P ] c [ Q ]
  → ⊢[ P ] c [ Q ]
completeness c cc = Conseq (fatto cc) (wp-hoare c) (λ r x → x)
