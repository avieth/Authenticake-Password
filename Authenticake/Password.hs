{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}

module Authenticake.Password (

    PasswordAuthenticator(..)
  , DigestComparison(..)
  , PasswordAuthenticationFailure(..)

  ) where

import Authenticake.Authenticate

data PasswordAuthenticator m s c d = PasswordAuthenticator {
    getDigest :: s -> m (Maybe d)
  , setDigest :: s -> Maybe c -> m ()
  , compareDigest :: s -> c -> d -> DigestComparison
  }

data DigestComparison = Match | NoMatch

data PasswordAuthenticationFailure
  = BadPassword
  | SubjectNotFound
  deriving (Show)

instance
    ( Monad m
    )
    => Authenticator (PasswordAuthenticator m s c d)

  where

    type NotAuthenticReason (PasswordAuthenticator m s c d) t = PasswordAuthenticationFailure
    type Subject (PasswordAuthenticator m s c d) t = s
    type Challenge (PasswordAuthenticator m s c d) t = c
    type AuthenticatorF (PasswordAuthenticator m s c d) = m

    authenticate authenticator proxy subject challenge = do
        maybeExistingDigest <- getDigest authenticator subject
        case maybeExistingDigest of
          Nothing -> return (Just SubjectNotFound)
          Just existingDigest ->
              case compareDigest authenticator subject challenge existingDigest of
                  Match -> return Nothing
                  NoMatch -> return (Just BadPassword)

