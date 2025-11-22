# ask
being a particular fragment of Haskell, extended to a proof system



# Installation

Ensure you have at most GHC 9.8.4 installed.

- ensure `$HOME/.cabal/bin` is in your `PATH`.
- run `cabal install` from the ask checkout directory.
- add the following lines to your `.emacs` file to automatically start `ask-mode` when you load an ask file.

```
(load-file "<path to ask>/ask/emacs/ask.el")
(require 'ask-mode)
(add-to-list 'auto-mode-alist '("\\.ask\\'" . ask-mode))
```

`<path to ask>` is the location where you cloned ask.
