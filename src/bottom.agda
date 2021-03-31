module bottom where

open import Level renaming (suc to lsuc ; zero to lzero)
open import Function.Base
open import IO

open import Text.Parser lzero using (runParserIO)

open import Data.List using (List ; _∷_ ; [])
open import Data.List.NonEmpty as List⁺ using (List⁺ ; _∷_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.String as String using (String ; _++_)

open import Bottom.Bottom
open import Bottom.Foreign.Haskell
open import Bottom.Parser


version = "0.1.0"

bottomify : String → IO {lzero} _
bottomify input = putStrLn ∘ render ∘ encodeBytes ∘ encodeUtf8 $ input

regress : String → IO _
regress input = do
  inj₂ text ← (decodeUtf8 ∘ List⁺.toList) <$> (runParserIO bottom input) where
    inj₁ (decodeError err) → putStrLn err
  putStrLn text

usageInfo : String
usageInfo
  =  "\nBottom translator " ++ version ++ "\n\n"
  ++ "Usage: bottom ((-b|--bottomify) | (-r|--regress) | (-v|--version) | (-h|--help)) <TEXT>\n"
  ++ "  Fantastic (maybe) CLI for translating between bottom and human-readable text\n\n"
  ++ "Available options:\n"
  ++ "  -b,--bottomify           Translate text to bottom\n"
  ++ "  -r,--regress             Translate bottom to human-readable text (futile)\n"
  ++ "  -v,--version             Prints version information\n"
  ++ "  -h,--help                Show this help text\n"

program : String → String → IO _
program "--bottomify" = bottomify
program "-b" = bottomify
program "--regress" = regress
program "-r" = regress
program "--version" _ = putStrLn ("Bottom translator " String.++ version)
program "-v" _ = putStrLn ("Bottom translator " String.++ version)
program _ _ = putStrLn usageInfo

main : Main
main = run do
  (opt ∷ txt ∷ _) ← getArgs where
    (opt ∷ []) → program opt ""
    [] → putStrLn usageInfo
  program opt txt
