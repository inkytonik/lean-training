# Lean training

## Usage

The best experience for interacting with Lean is via Visual Studio Code.
First, install the [Lean prover extension](https://marketplace.visualstudio.com/items?itemName=jroesch.lean).
Then open the top-level directory from this repository in VSCode.
Finally, open the relevant Lean source file (e.g., `src/training2.lean`).

The Lean extension will offer installing the Lean binaries and modifying your PATH - so don't install Lean yourself with `brew` or some such.

Afterwards, Lean will need to install the Mathlib library, which you can do with `leanproject get-mathlib-cache`.
You might have to restart VSCode after each step.

Finally you should be able to interact with the Lean code, modify, etc and you should see feedback from Lean in the editor.
