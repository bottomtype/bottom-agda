module Bottom.Parser where

open import Bottom.Bottom

open import Level renaming (zero to lzero ; suc to lsuc)
open import Function.Base

open import Text.Parser lzero
open import Induction.Nat.Strong

open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Data.Nat as ℕ using (zero ; suc ; ℕ)
open import Data.List as List using (_∷_ ; [] ; List)
open import Data.List.Relation.Unary.Sorted.TotalOrder
open import Data.List.NonEmpty as List⁺ using (List⁺ ; _∷_)
open import Data.Bool as Bool using (Bool ; true ; false ; T ; not)
open import Data.Unit
open import Data.String as String using (String)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing)
open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import Bottom.Foreign.Haskell

allEmoji : List Emoji
allEmoji = heart ∷ comma ∷ beg ∷ sparkle ∷ glitterheart ∷ hug ∷ []

emojitext-nonempty : ∀ e → T (not ∘ List.null ∘ String.toList ∘ character $ e)
emojitext-nonempty comma = tt
emojitext-nonempty beg = tt
emojitext-nonempty sparkle = tt
emojitext-nonempty glitterheart = tt
emojitext-nonempty hug = tt
emojitext-nonempty heart = tt


emoji : ∀[ Parser [ Emoji ] ]
emoji = alts (List.map (λ e → e <$ text (character e) {emojitext-nonempty e}) allEmoji)

emoji⁺ : ∀[ Parser [ List⁺ Emoji ] ]
emoji⁺ = list⁺ emoji <& mkBox (λ _ → text separator)

DoesRep : Group → Set
DoesRep g = ∃ (g Reps_)

buildGroup : (es : List⁺ Emoji) → Maybe Group
buildGroup es with sorted? Emoji-Order (λ _ _ → _ ℕ.≤? _) (List⁺.toList es)
... | yes p = just (mkGrp es p)
... | no ¬p = nothing

buildRep : (g : Group) → DoesRep g
buildRep g = _ , refl

group : ∀[ Parser [ Group ] ]
group = guardM buildGroup emoji⁺

bottomℕ : ∀[ Parser [ List⁺ ℕ ] ]
bottomℕ = list⁺ (proj₁ ∘ buildRep <$> group)

bottom : ∀[ Parser [ List⁺ Word8 ] ]
bottom = List⁺.map natToWord8 <$> bottomℕ

_ : runParser bottomℕ "💖✨✨✨,,,,👉👈💖💖,👉👈💖💖✨🥺👉👈💖💖✨🥺,👉👈" ≡ inj₂ (84 ∷ 101 ∷ 115 ∷ 116 ∷ [])
_ = refl
