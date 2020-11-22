module Elab where

import Bwd
import LexAsk

import Data.Map

import Tm

data Decl
  = DeclInfix
      Int        -- fixity level
      [String]   -- operators
  | DeclProp
      String
      (Tel ())
      [Intro]
  deriving Show

data Intro = (Pat, Pat) :<=: [Tel Tm] deriving Show


