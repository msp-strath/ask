module Ask.Src.Main where

import Ask.Src.ChkRaw

main :: IO ()
main = getContents >>= filth
