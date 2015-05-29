{-|
Module      : Authenticake.Password
Description : Non-volatile password auth using bcrypt and an RDBMS.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

module Authenticake.Password (

    PasswordAuthenticator
  , password

  , BCryptF
  , BCryptInterpreter
  , runBCryptInterpreter

  , HashingPolicy(..)
  , fastBcryptHashingPolicy
  , slowerBcryptHashingPolicy

  ) where

import Control.Applicative
import qualified Data.Text as T
import qualified Data.ByteString as BS
import Data.Text.Encoding (encodeUtf8)
import Data.Proxy
import Data.Relational
import Data.Relational.RelationalF
import Control.Monad.Free
import Control.Monad.FInterpreter
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Crypto.BCrypt hiding (hashPassword)
import Authenticake.Authenticate
import Authenticake.Secret

type SubjectColumn = '("subject", T.Text)
type DigestColumn = '("digest", BS.ByteString)
type PasswordSchema = '[ SubjectColumn, DigestColumn ]
type PasswordDatabase = '[ '("password", PasswordSchema) ]

subjectColumn :: Column SubjectColumn
subjectColumn = column

digestColumn :: Column DigestColumn
digestColumn = column

passwordSchema :: Schema PasswordSchema
passwordSchema = subjectColumn :| digestColumn :| EndSchema

passwordTable :: Table '("password", PasswordSchema)
passwordTable = Table Proxy passwordSchema

subjectCondition :: T.Text -> Condition '[ '[ SubjectColumn ] ]
subjectCondition subject = subjectColumn .==. subject .||. false .&&. true

challengeProjection :: Project '[ DigestColumn ]
challengeProjection = digestColumn :+| EndProject

makeRow :: T.Text -> BCryptDigest -> Row PasswordSchema
makeRow subject digest =
      (fromColumnAndValue subjectColumn subject)
  :&| (fromColumnAndValue digestColumn digest)
  :&| EndRow

type BCryptDigest = BS.ByteString

data BCryptF a = HashPassword HashingPolicy BS.ByteString (Maybe BS.ByteString -> a)

instance Functor BCryptF where
    fmap f term = case term of
        HashPassword policy pwd next -> HashPassword policy pwd (fmap f next)

newtype BCryptInterpreter m a = BCryptInterpreter {
    runBCryptInterpreter :: IdentityT m a
  } deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

instance FTrans BCryptInterpreter where
    transInterp interp = BCryptInterpreter . transInterp interp . fmap runBCryptInterpreter

instance MonadIO m => FInterpreter BCryptInterpreter m BCryptF where
    finterpret term = case term of
        HashPassword policy pwd next ->
            liftIO (hashPasswordUsingPolicy policy pwd) >>= next

hashPassword :: HashingPolicy -> BS.ByteString -> (Free BCryptF) (Maybe BS.ByteString)
hashPassword policy pwd = liftF (HashPassword policy pwd id)

type PasswordF = BCryptF :+: (RelationalF PasswordDatabase)

type PasswordAuthenticator i =
    SecretAuthenticator
      (Free PasswordF)
      T.Text
      -- Subject
      T.Text
      -- Challenge
      Maybe
      T.Text
      -- Authenticated thing = Subject
      (Const ())
      -- Cannot give an authenticated thing to set
      BCryptDigest

-- | A password authenticator using particular hashing policy.
--   The resulting monad is Free PasswordF, which contains a RelationalF.
--   To interpret that, be sure that PasswordDatabase is represented.
password
  :: forall i .
     ()
  => Proxy i
  -> HashingPolicy
  -> PasswordAuthenticator i
password proxy policy = SecretAuthenticator getDigest setDigest checkDigest

  where

    getDigest :: T.Text -> T.Text -> (Free PasswordF) (Maybe BCryptDigest)
    getDigest subject challenge =
        let select = Select passwordTable challengeProjection (subjectCondition subject)
            term :: Relational PasswordDatabase [Row '[DigestColumn]]
            term = rfselect select
        in  do rows <- injectF term
               case rows of
                   [] -> return Nothing
                   (digest :&| EndRow) : _ -> return (Just (fieldValue digest))

    setDigest :: T.Text -> Maybe T.Text -> Const () T.Text -> (Free PasswordF) ()
    setDigest subject mchallenge _ =
        let deleteTerm :: Relational PasswordDatabase ()
            deleteTerm = rfdelete (Delete passwordTable (subjectCondition subject))
            makeInsertion :: BS.ByteString -> Relational PasswordDatabase ()
            makeInsertion = \digest -> rfinsert (Insert passwordTable (makeRow subject digest))
        in  do injectF deleteTerm
               case mchallenge of
                   Nothing -> return ()
                   Just challenge -> do
                       mdigest <- injectF $ hashPassword policy (encodeUtf8 challenge)
                       case mdigest of
                           -- TODO how to handle this? Why would it ever fail?
                           Nothing -> error "BCrypt failed to generate a digest! Why?"
                           Just digest -> injectF $ makeInsertion digest

    checkDigest :: T.Text -> T.Text -> BCryptDigest -> (Free PasswordF) (Maybe T.Text)
    checkDigest subject challenge digest = do
        if not (validatePassword digest (encodeUtf8 challenge))
        then return Nothing
        else if hashUsesPolicy policy digest
             then return (Just subject)
             else setDigest subject (Just challenge) (Const ()) >> return (Just subject)
