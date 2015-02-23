{-
  Here we show how any Manifest can be used as an Authenticator to authenticate
  via password (salted whirlpool digest) any ManifestKey instance.

  The ingredients:

    type WithSaltedDigest a
    type PasswordAuthenticate manifest a
    type Password

  If you have a manifest of (WithSaltedDigest a) (i.e. some Manifest instance
  which is applied to a (WithSaltedDigest a)), and the type 'a' is a
  ManifestKey instance, then you get password authentication: just use your
  manifest to construct, via 'passwordAuthenticate', a value of type

    PasswordAuthenticate manifest a

  and use it in your authenticate and setAuthentication terms! The subject
  is your type 'a' and the challenge is Password.

-}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}

module Authenticake.Password (

    PasswordAuthenticate
  , passwordAuthenticate

  , PasswordAuthenticationFailure(..)
  , PasswordUpdateFailure(..)

  , Password
  , password
  , textPassword
  , stringPassword

  , WithSaltedDigest

  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import Control.RichConditional
import Data.TypeNat.Vect
import Data.Proxy
import qualified Crypto.Hash as H
import Crypto.Random
import Data.Byteable (toBytes)
import Manifest.Manifest
import Authenticake.Authenticate

-- | An Authenticator, which relies on a given manifest and the type of
--   thing to be authenticated. We might see, for instance
--
--     :: PasswordAuthenticate PostgreSQL User
--
data PasswordAuthenticate manifest a = PasswordAuthenticate (manifest (WithSaltedDigest a))

-- | Any manifest which has not yet been specialized can be used to make
--   a PasswordAuthenticate.
passwordAuthenticate :: Manifest manifest => (forall b . manifest b) -> PasswordAuthenticate manifest a
passwordAuthenticate m = PasswordAuthenticate m

newtype Password = Password {
    unPassword :: BS.ByteString
  }

textPassword :: T.Text -> Password
textPassword = Password . encodeUtf8

stringPassword :: String -> Password
stringPassword = Password . B8.pack

password :: BS.ByteString -> Password
password = Password

newtype Digest = Digest {
    unDigest :: BS.ByteString
  } deriving (Eq)

newtype Salt = Salt {
    unSalt :: BS.ByteString
  }

newtype SaltedDigest = SaltedDigest {
    unSaltedDigest :: (Salt, Digest)
  }

newtype WithSaltedDigest a = WithSaltedDigest {
    unWithSaltedDigest :: (a, SaltedDigest)
  }

newtype SaltedDigestMatch = SaltedDigestMatch {
    unSaltedDigestMatch :: (BS.ByteString, SaltedDigest)
  }

matchSaltedDigest :: BS.ByteString -> SaltedDigest -> Maybe SaltedDigestMatch
matchSaltedDigest bs s@(SaltedDigest (salt, digest)) =
    let SaltedDigest (salt', digest') = generateSaltedDigest bs salt
    in  if digest' /= digest then Nothing else Just (SaltedDigestMatch (bs, s))

-- | Generate a Whirlpool digest of a given ByteString.
generateDigest :: BS.ByteString -> Digest
generateDigest = Digest . toBytes . whirlpoolHash
  where
    whirlpoolHash :: BS.ByteString -> H.Digest H.Whirlpool
    whirlpoolHash = H.hash

-- | Generate a SaltedDigest for a given ByteString and Salt.
generateSaltedDigest :: BS.ByteString -> Salt -> SaltedDigest
generateSaltedDigest bs salt =
    let digest = generateDigest (BS.append bs (unSalt salt))
    in  SaltedDigest (salt, digest)

-- | Generate a salt of a given length (in bytes)
generateSalt :: Int -> IO Salt
generateSalt l = do
  ep <- createEntropyPool
  let gen = cprgCreate ep :: SystemRNG
  let (bytes, _) = cprgGenerate l gen
  return $ Salt bytes

-- | A SaltedDigest can be used as a value in a Manifest.
instance ManifestValue SaltedDigest where

  type ManifestValueLength SaltedDigest = Two

  manifestibleValueDump (SaltedDigest (salt, digest)) = VCons bsalt (VCons bdigest VNil)
    where
      bsalt = unSalt salt
      bdigest = unDigest digest

  manifestibleValuePull bss = case bss of
    VCons bsalt (VCons bdigest VNil) -> Just $ SaltedDigest (Salt bsalt, Digest bdigest)
    _ -> Nothing

-- | A WithSaltedDigest is Manifestible, so long as its type argument is a
--   ManifestKey.
instance ManifestKey a => Manifestible (WithSaltedDigest a) where

  type ManifestibleKey (WithSaltedDigest a) = a
  type ManifestibleValue (WithSaltedDigest a) = SaltedDigest

  manifestibleKey (WithSaltedDigest (x, _)) = x
  manifestibleValue (WithSaltedDigest (_, x)) = x
  manifestibleFactorization key value = WithSaltedDigest (key, value)

data PasswordAuthenticationFailure manifest
  = BadPassword
  | SubjectNotFound
  | OtherFailure (ManifestFailure manifest)

data PasswordUpdateFailure manifest
  = OtherUpdateFailure (ManifestFailure manifest)

instance
  ( ManifestKey a
  , Manifest manifest
  , Monad (ManifestMonad manifest)
  )
  => Authenticator (PasswordAuthenticate manifest a) where

  type Failure (PasswordAuthenticate manifest a) s = PasswordAuthenticationFailure manifest
  type Subject (PasswordAuthenticate manifest a) t = a
  type Challenge (PasswordAuthenticate manifest a) s = Password

  authenticatorDecision (PasswordAuthenticate m) proxy subject challenge = do
      (outcome, _) <- manifest m (mget subject (undefined :: Proxy (manifest (WithSaltedDigest a))))
      return $ case outcome of
        Left manifestFailure -> Just (OtherFailure manifestFailure)
        -- Use the salt to hash the challenge and compare it with the digest.
        Right manifestRead ->
            (inCase manifestRead)
            (ifFound)
            (ifNotFound)

    where

      ifNotFound :: Maybe (Failure (PasswordAuthenticate manifest a) (Subject (PasswordAuthenticate manifest a) a))
      ifNotFound = Just (SubjectNotFound)

      ifFound :: WithSaltedDigest a -> Maybe (Failure (PasswordAuthenticate manifest a) (Subject (PasswordAuthenticate manifest a) a))
      ifFound (WithSaltedDigest (x, saltedDigest)) =
          (inCase (matchSaltedDigest (unPassword challenge) saltedDigest))
          (ifMatch)
          (ifNoMatch)

      ifMatch :: SaltedDigestMatch -> Maybe (Failure (PasswordAuthenticate manifest a) (Subject (PasswordAuthenticate manifest a) a))
      ifMatch _ = Nothing

      ifNoMatch :: Maybe (Failure (PasswordAuthenticate manifest a) (Subject (PasswordAuthenticate manifest a) a))
      ifNoMatch = Just BadPassword

instance
  ( ManifestKey a
  , Manifest manifest
  , Monad (ManifestMonad manifest)
  )
  => MutableAuthenticator (PasswordAuthenticate manifest a) where

  type UpdateFailure (PasswordAuthenticate manifest a) s = PasswordUpdateFailure manifest

  authenticatorUpdate (PasswordAuthenticate m) proxy subject challenge = do
      salt <- generateSalt 4
      let saltedDigest = generateSaltedDigest (unPassword challenge) salt
      let withSaltedDigest = WithSaltedDigest (subject, saltedDigest)
      (outcome, newManifest) <- manifest m (mput withSaltedDigest (undefined :: Proxy manifest))
      return $ case outcome of
        Left manifestFailure -> Left (OtherUpdateFailure manifestFailure)
        Right manifestWrite -> Right (PasswordAuthenticate newManifest)
