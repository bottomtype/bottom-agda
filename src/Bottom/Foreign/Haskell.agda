module Bottom.Foreign.Haskell where

{-# FOREIGN GHC
  {-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
#-}


open import Foreign.Haskell
open import Foreign.Haskell.Coerce
open import Level
import Data.List as STD
import Data.Nat as STD
open import Agda.Builtin.String
open import Data.Sum as STD
import IO.Primitive as IO
import IO as STD

{-# FOREIGN GHC

  import System.Environment
  import qualified Data.ByteString as BS
  import Data.Word (Word8)
  import qualified Data.Text.Encoding as Text
  import qualified Data.Text.Encoding.Error as Text

  type AgdaList l a = [a]

  data AgdaUnicodeException = DecodeError Data.Text.Text


  agdaDecodeUtf8 xs = case Text.decodeUtf8' (BS.pack xs) of
    Left (Text.DecodeError err _) -> Left (DecodeError (Data.Text.pack err))
    Right txt -> Right txt

#-}

private
  variable
    a b : Level
    A : Set a
    B : Set b


postulate

  Word8 : Set
  word8ToNat : Word8 → STD.ℕ
  natToWord8 : STD.ℕ → Word8


data UnicodeException : Set where
  decodeError : String → UnicodeException

private

  data List (A : Set a) : Set a where
    [] : List A
    _∷_ : A → List A → List A

  instance

    list-toFFI : Coercible (STD.List A) (List A)
    list-toFFI = TrustMe

    list-fromFFI : Coercible (List A) (STD.List A)
    list-fromFFI = TrustMe

  postulate

    primEncodeUtf8 : String → List Word8
    primDecodeUtf8 : List Word8 → Either UnicodeException String

    primGetArgs : IO.IO (List String)


{-# COMPILE GHC List = data AgdaList ([] | (:)) #-}
{-# COMPILE GHC UnicodeException = data AgdaUnicodeException (DecodeError) #-}


{-# COMPILE GHC Word8 = type Word8 #-}
{-# COMPILE GHC primEncodeUtf8 = \str -> BS.unpack (Text.encodeUtf8 str) #-}
{-# COMPILE GHC primDecodeUtf8 = agdaDecodeUtf8 #-}
{-# COMPILE GHC word8ToNat = fromIntegral #-}
{-# COMPILE GHC natToWord8 = fromIntegral #-}
{-# COMPILE GHC primGetArgs = fmap (fmap Data.Text.pack) getArgs #-}


encodeUtf8 : String → STD.List Word8
encodeUtf8 str = coerce (primEncodeUtf8 str)

decodeUtf8 : STD.List Word8 → UnicodeException ⊎ String
decodeUtf8 xs = coerce (primDecodeUtf8 (coerce xs))

getArgs : STD.IO (STD.List String)
getArgs = coerce STD.<$> STD.lift primGetArgs
