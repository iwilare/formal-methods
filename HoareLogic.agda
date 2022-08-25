open import Data.Nat using ()
open import Data.Bool using (true; false)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_)
open import Data.Empty using ()
open import Level using (suc; _⊔_)
open import Relation.Nullary           using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import IMP
open import OperationalSemantics

assn : ∀{l} → Set (suc l)
assn {a} = state → Set a

data ⊢[_]_[_] {l} : assn {l} → com → assn {l} → Set (suc l) where
  Skip : ∀{P}
     → ⊢[ P ] SKIP [ P ]
  Loc : ∀{Q a x}
     → ⊢[ (λ s → Q (s [ x ::= aval a s ])) ] (x ::= a) [ Q ]
  Comp : ∀{P Q R c₁ c₂}
     → ⊢[ P ] c₁ [ Q ]
     → ⊢[ Q ] c₂ [ R ]
     → ⊢[ P ] c₁ :: c₂ [ R ]
  If : ∀{P b c₁ Q c₂}
     → ⊢[ (λ s → P s × bval b s ≡ true)  ] c₁ [ Q ]
     → ⊢[ (λ s → P s × bval b s ≡ false) ] c₂ [ Q ]
     → ⊢[ P ] (IF b THEN c₁ ELSE c₂) [ Q ]
  While : ∀{P b c}
     → ⊢[ (λ s → P s × bval b s ≡ true) ] c [ P ]
     → ⊢[ P ] (WHILE b DO c) [ (λ s → P s × bval b s ≡ false) ]
  Conseq : ∀{P Q P′ Q′ : assn} {c}
     → (∀ s → P′ s → P s)
     → ⊢[ P  ] c [ Q  ]
     → (∀ s → Q s → Q′ s)
     → ⊢[ P′ ] c [ Q′ ]

⊨[_]_[_] : assn → com → assn → Set
⊨[ P ] c [ Q ] = ∀{s t} → P s → ⦅ c , s ⦆⇒ t → Q t

soundness : ∀{P Q : assn} {c}
          → ⊢[ P ] c [ Q ]
          → ⊨[ P ] c [ Q ]
soundness Skip p Skip = p
soundness Loc p Loc = p
soundness (Comp r r₁) p (Comp z z₁) = soundness r₁ (soundness r p z) z₁
soundness (If r r₁) p (IfTrue x s) = soundness r (p , x) s
soundness (If r r₁) p (IfFalse x s) = soundness r₁ (p , x) s
soundness (While r) p (WhileFalse x₁) = p , x₁
soundness (While r) p (WhileTrue x₁ s s₁) = soundness (While r) (soundness r (p , x₁) s) s₁
soundness (Conseq x₁ r x₂) {s₁} {t} p s = x₂ t (soundness r (x₁ s₁ p) s)

wp : ∀{l} → com → assn {l} → assn {l}
wp c Q s = ∀ t → ⦅ c , s ⦆⇒ t → Q t

validity-wp : ∀{P Q : assn} {c}
      → ⊨[ P ] c [ Q ]
      → (∀ s → P s → wp c Q s)
validity-wp = λ z s z₁ t → z z₁

validity-wp-converse : ∀{P Q : assn} {c}
      → (∀ s → P s → wp c Q s)
      → ⊨[ P ] c [ Q ]
validity-wp-converse = (λ z {s} {t} z₁ → z s z₁ t)

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
completeness c cc = Conseq (validity-wp cc) (wp-hoare c) (λ r x → x)
