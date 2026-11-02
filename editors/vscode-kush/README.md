# Kush editor syntax

This directory contains a grammar-only VS Code extension for `.kush` files:

- TextMate syntax highlighting (`syntaxes/kush.tmLanguage.json`);
- language registration and bracket/comment configuration.

It is not full editor tooling. There is no language server, live diagnostic
squiggle, completion, or go-to-definition yet. Use the compiler for diagnostics:

```sh
kush check
kush test
kush fmt --check
```

To try the extension, open this directory in VS Code and use
**Extensions: Install Extension from Location...**, or copy/symlink the directory
into your VS Code extensions directory. The extension has no runtime code and
does not invoke the compiler.
