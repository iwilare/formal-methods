open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function.Equivalence using (_⇔_; equivalence; Equivalence)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)

open import IMP
open import OperationalSemantics
open import Hoare

wp : ∀{l} → com → assn {l} → assn {l}
wp c Q s = ∀ t → ⦅ c , s ⦆⇒ t → Q t

fatto : ∀{P Q : assn} {c}
      → ⊨[ P ] c [ Q ]
      → (∀ s → P s → wp c Q s)
fatto = λ z s z₁ t → z z₁

fatto-converse : ∀{P Q : assn} {c}
      → (∀ s → P s → wp c Q s)
      → ⊨[ P ] c [ Q ]
fatto-converse = (λ z {s} {t} z₁ → z s z₁ t)

wp-hoare : ∀ c {l} {Q : assn {l}}
  → ⊢[ wp c Q ] c [ Q ]
wp-hoare SKIP = Conseq (λ s z → z s Skip) Skip (λ s z → z)
wp-hoare (x ::= a) = Conseq (λ s wpe → wpe (s [ x ::= aval a s ]) Loc) Loc (λ s r → r)
wp-hoare (c :: c₁) = Comp (Conseq (λ s z x x₁ x₂ x₃ → z x₂ (Comp x₁ x₃)) (wp-hoare c) (λ s z → z)) (wp-hoare c₁)
wp-hoare (IF x THEN c ELSE c₁) = If (Conseq (λ s z x x₁ → proj₁ z x (IfTrue (proj₂ z) x₁)) (wp-hoare c) (λ s z → z))
                                    (Conseq (λ s z x x₁ → proj₁ z x (IfFalse (proj₂ z) x₁)) (wp-hoare c₁) (λ s z → z))
wp-hoare (WHILE b DO c) =
  Conseq (λ s x → x)
         (While (Conseq (λ s z x x₁ x₂ x₃ → proj₁ z x₂ (WhileTrue (proj₂ z) x₁ x₃))
                        (wp-hoare c)
                        (λ s z → z)))
         (λ s z → proj₁ z s (WhileFalse (proj₂ z)))

completeness : ∀ c {P Q : assn}
  → ⊨[ P ] c [ Q ]
  → ⊢[ P ] c [ Q ]
completeness c cc = Conseq (fatto cc) (wp-hoare c) (λ r x → x)
