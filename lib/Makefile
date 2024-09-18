default: ../bin/ask

../bin/ask: OddEven.hs Bwd.hs HalfZip.hs Lexing.hs Parsing.hs Glueing.hs Printing.hs RawAsk.hs Thin.hs Tm.hs HardwiredRules.hs Typing.hs ChkRaw.hs Main.hs
	pushd ../.. ;  ghc --make -o ask/bin/ask ask/Src/Main.hs -main-is Ask.Src.Main.main ;  popd
