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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module Authenticake.Password (

    PasswordAuthenticator
  , password

  , HashingPolicy(..)
  , fastBcryptHashingPolicy
  , slowerBcryptHashingPolicy

  ) where

import Control.Monad.IO.Class
import qualified Data.Text as T
import qualified Data.ByteString as BS
import Data.Text.Encoding (encodeUtf8)
import Data.Proxy
import Data.Relational
import Data.Relational.Universe
import Data.Relational.Interpreter
import Crypto.BCrypt
import Authenticake.Authenticate
import Authenticake.Secret

type SubjectColumn = '("subject", T.Text)
type DigestColumng = '("digest", BS.ByteString)
type PasswordSchema = '[ SubjectColumn, DigestColumng ]

subjectColumn :: Column SubjectColumn
subjectColumn = column

digestColumn :: Column DigestColumng
digestColumn = column

passwordSchema :: Schema PasswordSchema
passwordSchema = subjectColumn :| digestColumn :| EndSchema

passwordTable :: Table '("password", PasswordSchema)
passwordTable = Table Proxy passwordSchema

subjectCondition :: T.Text -> Condition '[ '[ SubjectColumn ] ]
subjectCondition subject = subjectColumn .==. subject .||. false .&&. true

challengeProjection :: Project '[ DigestColumng ]
challengeProjection = digestColumn :+| EndProject

makeRow :: T.Text -> BCryptDigest -> Row PasswordSchema
makeRow subject digest =
      (fromColumnAndValue subjectColumn subject)
  :&| (fromColumnAndValue digestColumn digest)
  :&| EndRow

type PasswordAuthenticator i =
    SecretAuthenticator
      (InterpreterMonad i)
      T.Text
      T.Text
      BCryptDigest
      T.Text

type BCryptDigest = BS.ByteString

-- | A password authenticator using a particular relational interpreter
--   and hashing policy.
--   The existence of a table corresponding to passwordTable is assumed.
password
  :: forall i .
     ( RelationalInterpreter i
     , Functor (InterpreterMonad i)
     , Monad (InterpreterMonad i)
     , MonadIO (InterpreterMonad i)
     , InterpreterSelectConstraint i PasswordSchema '[DigestColumng] '[ '[SubjectColumn] ]
     , InterpreterInsertConstraint i PasswordSchema
     , InterpreterDeleteConstraint i PasswordSchema '[ '[SubjectColumn] ]
     , InUniverse (Universe i) BS.ByteString
     , InUniverse (Universe i) T.Text
     )
  => Proxy i
  -> HashingPolicy
  -> PasswordAuthenticator i
password proxy policy = SecretAuthenticator getDigest setDigest checkDigest

  where

    getDigest :: T.Text -> T.Text -> (InterpreterMonad i) (Maybe BCryptDigest)
    getDigest subject challenge = do
        rows <- interpretSelect' proxy (Select passwordTable challengeProjection (subjectCondition subject))
        let rows' = rows >>= maybe [] return
        case rows' of
            [] -> return Nothing
            (digest :&| EndRow) : _ -> return (Just (fieldValue digest))

    setDigest :: T.Text -> Maybe T.Text -> T.Text -> (InterpreterMonad i) ()
    setDigest subject mchallenge thing = do
        interpretDelete proxy (Delete passwordTable (subjectCondition subject))
        case mchallenge of
            Nothing -> return ()
            Just challenge -> do
                mdigest <- liftIO (hashPasswordUsingPolicy policy (encodeUtf8 challenge))
                case mdigest of
                    Nothing -> error "BCrypt failed to generate a digest!"
                    Just digest -> interpretInsert proxy (Insert passwordTable (makeRow subject digest))

    checkDigest :: T.Text -> T.Text -> BCryptDigest -> (InterpreterMonad i) (Maybe T.Text)
    checkDigest subject challenge digest = do
        if not (validatePassword digest (encodeUtf8 challenge))
        then return Nothing
        else if hashUsesPolicy policy digest
             then return (Just subject)
             else setDigest subject (Just challenge) subject >> return (Just subject)
