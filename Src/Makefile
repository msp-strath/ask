default: ../bin/ask

../bin/ask: Bwd.hs HalfZip.hs LexAsk.hs ParTok.hs RawAsk.hs Thin.hs Tm.hs ChkRaw.hs Main.hs
	pushd ../.. ;  ghc --make -o ask/bin/ask ask/Src/Main.hs -main-is Ask.Src.Main.main ;  popd
