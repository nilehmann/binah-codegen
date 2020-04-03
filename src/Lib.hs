{-# LANGUAGE OverloadedStrings #-}

{-# LANGUAGE QuasiQuotes #-}

module Lib where

import           Data.Either
import           Text.Megaparsec         hiding ( parse )
import           Text.RawString.QQ

import           Ast
import           Parser

parse = fromRight (Decls []) $ runParser
  (decls <* eof)
  ""
  [r|
predicate friends :: UserId -> UserId -> Bool

User
  name Text
  username Text

Wish

  description Text @PublicOrFriends
  accessLevel String

Friendship
  user1 UserId
  user2 UserId

  assert [friends user1 user2]

policy PublicOrFriends = \wish viewer ->
   wishAccessLevel wish == "public" ||
   wishOwner wish == entityKey viewer ||
   (wishAccessLevel wish == "friends"
     && friends (wishOwner wish) (entityKey viewer))
|]
