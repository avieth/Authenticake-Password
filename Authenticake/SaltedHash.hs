{-|
Module      : 
Description : 
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}

module Authenticake.SaltedHash (

    matchSaltedHash
  , generateSalt
  , generateSaltedHash

  ) where

import qualified Data.ByteString as BS
import qualified Crypto.Hash as H
import Crypto.Random
import Data.Byteable (toBytes)
import Authenticake.Password

matchSaltedHash :: BS.ByteString -> SaltedHash -> DigestComparison
matchSaltedHash bs s@(SaltedHash (salt, hash)) =
    let SaltedHash (_, hash') = generateSaltedHash bs salt
    in  if hash' /= hash
        then NoMatch
        else Match

generateHash :: BS.ByteString -> Hash
generateHash = Hash . toBytes . whirlpoolHash
  where
    whirlpoolHash :: BS.ByteString -> H.Digest H.Whirlpool
    whirlpoolHash = H.hash

newtype Hash = Hash {
    unHash :: BS.ByteString
  } deriving (Eq)

newtype Salt = Salt {
    unSalt :: BS.ByteString
  }

newtype SaltedHash = SaltedHash {
    unSaltedHash :: (Salt, Hash)
  }

generateSaltedHash :: BS.ByteString -> Salt -> SaltedHash
generateSaltedHash bs salt =
    let hash = generateHash (BS.append bs (unSalt salt))
    in  SaltedHash (salt, hash)

generateSalt :: Int -> IO Salt
generateSalt l = do
  ep <- createEntropyPool
  let gen = cprgCreate ep :: SystemRNG
  let (bytes, _) = cprgGenerate l gen
  return $ Salt bytes
