open import Data.Product using (_×_; _,_)

open import IMP
open import OperationalSemantics
open import Hoare

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
