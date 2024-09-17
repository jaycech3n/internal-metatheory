{-# OPTIONS --without-K --rewriting #-}

module cwfs.StandardModel where

open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

𝒯 : WildCategory _ _
WildCategory.Ob 𝒯 = Type₁
WildCategoryStructure.wildsemicatstr (WildCategory.wildcatstr 𝒯) = record
  { hom = λ A B → A → B
  ; _◦_ = λ g f a → g (f a)
  ; ass = idp }
WildCategoryStructure.id (WildCategory.wildcatstr 𝒯) {A} = idf A
WildCategoryStructure.idl (WildCategory.wildcatstr 𝒯) f = idp
WildCategoryStructure.idr (WildCategory.wildcatstr 𝒯) f = idp

𝒯-ctxstr : ContextStructure 𝒯
ContextStructure.◆ 𝒯-ctxstr = ⊤₁
ContextStructure.◆-terminal 𝒯-ctxstr A = Π-level λ _ → ⊤₁-level

𝒯-tytmstr : TyTmStructure 𝒯
𝒯-tytmstr = record
  { ctxstr = 𝒯-ctxstr
  ; Ty = λ A → A → Type₁
  ; _[_] = λ P f → P ∘ f
  ; [id] = idp
  ; [◦] = idp
  ; Tm = λ {A} P → (a : A) → P a
  ; _[_]ₜ = λ g f → g ∘ f
  ; [id]ₜ = idp
  ; [◦]ₜ = idp }

𝒞 : CwFStructure 𝒯
CwFStructure.compstr 𝒞 = record
  { tytmstr = 𝒯-tytmstr
  ; _∷_ = λ A P → Σ A P
  ; π = λ _ → fst
  ; υ = λ _ → snd
  ; _,,_ = λ f g γ → f γ , g γ
  ; βπ = idp
  ; βυ = idp
  ; η,, = idp
  ; ,,-◦ = idp }

𝒫 : PiStructure 𝒞
𝒫 = record
  { Π′ = λ P Q a → (((p : P a) → Q (a , p)) :> Type₁)
  ; λ′ = curry
  ; app = uncurry
  ; βΠ′ = λ f → idp
  ; ηΠ′ = λ f → idp
  ; Π′[] = idp
  ; λ′[]ₜ = idp }

𝒰 : UniverseStructure 𝒞
𝒰 = record
  { U = λ _ → Type₀
  ; el = λ s a → Lift (s a)
  ; U[] = idp
  ; el[] = idp }
