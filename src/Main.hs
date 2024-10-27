{-# LANGUAGE LambdaCase #-}

module Main where

import System.Environment
import Data.Traversable

import Language.Ask.ChkRaw

main :: IO ()
main = getArgs >>= \case
  [] -> interact filth
  xs -> do
    inp <- concat <$> traverse readFile xs
    putStr $ filth inp
