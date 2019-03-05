module PosetAdjunctions where

{- aka Galois Connections. -}

open import Relation.Binary
open import Level

{- Defining the monotonic map concept using records. -}

record IsMonotonicMap {c ℓ₁ ℓ₂} (A B : Poset c ℓ₁ ℓ₂) (f : Poset.Carrier A -> Poset.Carrier B) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isMonotonic : ∀ {x y : Poset.Carrier A} -> Poset._≤_ A x y → Poset._≤_ B (f x) (f y)

record MonotonicMap {c ℓ₁ ℓ₂} (A B : Poset c ℓ₁ ℓ₂) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    f : Poset.Carrier A -> Poset.Carrier B
    prop : IsMonotonicMap A B f

{- Example of a monotonic map. -}

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties

monsuc : IsMonotonicMap ≤-poset ≤-poset ℕ.suc
monsuc = record { isMonotonic = s≤s }

{- Proving equivalence between two poset adjunction definitions. -}

record IsAdjunctionViaDef1 {c ℓ₁ ℓ₂} (A B : Poset c ℓ₁ ℓ₂) (monf : MonotonicMap A B) (mong : MonotonicMap B A) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    relationshipOne : ∀ {x : Poset.Carrier A} {y : Poset.Carrier B} → Poset._≤_ A x (MonotonicMap.f mong y) → Poset._≤_ B (MonotonicMap.f monf x) y
    relationshipTwo : ∀ {x : Poset.Carrier A} {y : Poset.Carrier B} → Poset._≤_ B (MonotonicMap.f monf x) y → Poset._≤_ A x (MonotonicMap.f mong y)

record IsAdjunctionViaDef2 {c ℓ₁ ℓ₂} (A B : Poset c ℓ₁ ℓ₂) (monf : MonotonicMap A B) (mong : MonotonicMap B A)  : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    gf : ∀ (x : Poset.Carrier A) → Poset._≤_ A x (MonotonicMap.f mong (MonotonicMap.f monf x))
    fg : ∀ (x : Poset.Carrier B) → Poset._≤_ B (MonotonicMap.f monf (MonotonicMap.f mong x)) x

{- The syntax isn't particularly pretty. TODO: find out how to improve it. -}

open import Relation.Binary.PartialOrderReasoning

lemma_equiv₁ : ∀ {c ℓ₁ ℓ₂} (A B : Poset c ℓ₁ ℓ₂) → (monf : MonotonicMap A B) → (mong : MonotonicMap B A) → IsAdjunctionViaDef1 A B monf mong → IsAdjunctionViaDef2 A B monf mong
lemma_equiv₁ A B monf mong record { relationshipOne = relationshipOne ; relationshipTwo = relationshipTwo } =
  record {
    gf = λ x → relationshipTwo (Poset.refl B) ;
    fg = λ x → relationshipOne (Poset.refl A) }

lemma_equiv₂ : ∀ {c ℓ₁ ℓ₂} (A B : Poset c ℓ₁ ℓ₂) → (monf : MonotonicMap A B) → (mong : MonotonicMap B A) → IsAdjunctionViaDef2 A B monf mong → IsAdjunctionViaDef1 A B monf mong
lemma_equiv₂ A B monf mong record { gf = gf ; fg = fg } =
  record {
    relationshipOne   = λ {x} {y} x≤gy →
      RB.begin MonotonicMap.f monf x RB.≤⟨ IsMonotonicMap.isMonotonic (MonotonicMap.prop monf) x≤gy ⟩
               MonotonicMap.f monf (MonotonicMap.f mong y) RB.≤⟨ fg y ⟩
               y RB.∎ ;
    relationshipTwo = λ {x} {y} fx≤y →
      RA.begin x RA.≤⟨ gf x ⟩
               MonotonicMap.f mong (MonotonicMap.f monf x) RA.≤⟨ IsMonotonicMap.isMonotonic (MonotonicMap.prop mong) fx≤y ⟩
               MonotonicMap.f mong y RA.∎  }
          where open module RA = Relation.Binary.PartialOrderReasoning A
                open module RB = Relation.Binary.PartialOrderReasoning B

{- Done. -}
