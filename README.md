Experimenting with lean4.



Below are very basic things to get you started like setup and basic docs/resources. The rest of this
repo is readme-equipped folders containing lean4 projects trying to showcase something. They are
discussed in Section [Experimentalean4](#experimentalean4).



## Ecosystem and Setup

The lean 4 ecosystem is composed of three things:
- [`elan`](https://github.com/leanprover/elan):
    toolchain (versioning) manager. Similar to (fork of) rust's `rustup`, allows to
    download/update official toolchains, set a default, override the default toolchain in specific
    directories, set (pin) a toolchain name to a local build.
- [`lake`](https://github.com/leanprover/lake):
    project manager (also LSP). Similar to (but not a fork of) rust's `cargo`, compiles
    sources organized in a specific layout based on a project configuration file. Handles
    dependencies too, probably a bit experimental at this point.
- [`lean`/`leanc`](https://github.com/leanprover/lean4):
    compiler/LSP. It does compiling and LSP-ing.
- VS Code for editing with the `lean4` plugin. For anything else, have fun setting up LSP /
  proof-info view / UTF-8, failing, and then setting up VS Code.



**Setup** is basically just installing `elan` since it handles everything else. Support for Apple
silicon is currently in nightly and is discussed last:
- manual setup:
    https://github.com/leanprover/elan#manual-installation
- on x86 macos `brew install elan-init`
- probably on `pacman` on ArchLinux
- probably installable with `apt-get` or whatever on windows-like broken systems (ubuntu *etc.*)

On Apple silicon, do **not** follow the M1-specific [manual setup
instructions](https://github.com/leanprover/elan#manual-installation). Lean 4 supports Apple silicon
(in nightly), installing `elan` as interpreted x86 is either completely out-of-date or utterly idiotic.

Basically, you need to install `elan` **without** actually installing a toolchain. Otherwise, `elan`
will try to get the stable toolchain which will fail as Apple silicon is currently in nightly.
Precise instructions are unstable (**because nigthly**), but `brew install elan-init` and then
running `elan-init` should give you the opportunity to perform the init without installing stable.
Then run `elan default leanprover/lean4:nightly`, though you can try `elan default
leanprover/lean4:stable` in case Apple silicon reached stable.



## Resources

**Official page**: `github.io` lean 4 page
- https://leanprover.github.io
Includes *ongoing* WIP [learning material](https://leanprover.github.io/documentation)
- *Theorem Proving in Lean 4*: https://leanprover.github.io/theorem_proving_in_lean4
- *Lean 4 Manual*: https://leanprover.github.io/lean4/doc



**Mathlib4**: documentation for lean 4's stdlib, and *mathlib4* which is the *ongoing* port of
mathlib3, lean3's heavy-duty math stdlib:
- https://leanprover-community.github.io/mathlib4_docs



**Coq/lean/cheatsheet**: relates coq and lean 3~4 tactics:
- https://github.com/jldodds/coq-lean-cheatsheet
This is insanely useful as it allows finding lean tactics from coq-based resources; namely, the coq
tactics
- cheatsheet https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html
- and index https://coq.inria.fr/refman/coq-tacindex.html



**Beyond Notations**: awesome readable paper about lean 4's *syntax extensions*. Absolute must-read:
- https://arxiv.org/abs/2001.10490



## Experimentalean4

Here are the projects of this repo, ordered from most to least basics with a short description.

- [`filesAndNamespaces`](./filesAndNamespaces):
    Lean 4 is a modern language so, in a project, the way sources are layed out on your filesystem
    carries meaning. You cannot do anything non-trivial without understanding this first, and then
    you need to understand how *namespaces* work. *"Namespace"* is exactly the same as *"module"*
    since lean does not have functors.

    This project also discusses the `import` mecanics.
