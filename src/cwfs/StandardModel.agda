{-# OPTIONS --without-K --rewriting #-}

module cwfs.StandardModel where

open import cwfs.CwFs

𝒯 : WildCategory _ _
WildCategory.Ob 𝒯 = Type₀
WildCategoryStructure.wildsemicatstr (WildCategory.wildcatstr 𝒯) = record
  { hom = λ A B → A → B
  ; _◦_ = λ g f a → g (f a)
  ; ass = idp }
WildCategoryStructure.id (WildCategory.wildcatstr 𝒯) {A} = idf A
WildCategoryStructure.idl (WildCategory.wildcatstr 𝒯) = idp
WildCategoryStructure.idr (WildCategory.wildcatstr 𝒯) = idp

𝒯-ctxstr : ContextStructure 𝒯
ContextStructure.◆ 𝒯-ctxstr = ⊤
ContextStructure.◆-terminal 𝒯-ctxstr A = Π-level λ _ → Unit-level

𝒯-tytmstr : TyTmStructure 𝒯
𝒯-tytmstr = record
  { ctxstr = 𝒯-ctxstr
  ; Ty = λ A → A → Type₀
  ; _[_] = λ {A} {B} P f → P ∘ f
  ; [id] = idp
  ; [◦] = idp
  ; Tm = λ {A} P → (a : A) → P a
  ; _[_]ₜ = λ {A} {B} {P} g f → g ∘ f
  ; [id]ₜ = idp
  ; [◦]ₜ = idp }

𝒰 : CwFStructure 𝒯
CwFStructure.compstr 𝒰 = record
  { tytmstr = 𝒯-tytmstr
  ; _∷_ = λ A P → Σ A P
  ; π = λ _ → fst
  ; υ = λ _ → snd
  ; _,,_ = λ {A} {B} {P} f g a → f a , g a
  ; βπ = idp
  ; βυ = idp
  ; η,, = idp
  ; ,,-◦ = idp }
