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
