---
title: Coq Tutorial
date: 2023-10-05
tags: ["category theory", "haskell"]
subtitle: Interactive Theorem Proving with Coq and Coqtop REPL
mathjax: true
---
{% raw %}
<script>
  MathJax = {
    loader: {
      load: ['[custom]/xypic.js'],
      paths: {custom: 'https://beuke.org/js'}
    },
    tex: {
      packages: {'[+]': ['xypic']}
    }
  };
</script>

<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3.1.4/es5/tex-chtml-full.js"></script>
<script>
window.addEventListener('load', function() {
   document.querySelectorAll("mjx-xypic-object").forEach( (x) => (x.style.color = "var(--darkreader-text--text"));
   document.querySelectorAll("mjx-math > mjx-xypic > svg > g").forEach(x => x.setAttribute("stroke", "var(--darkreader-text--text"))
})
</script>

{% endraw %}

Coq is a proof management system that provides a formal language to write mathematical definitions, executable algorithms, and theorems together with an environment for semi-interactive development of machine-checked proofs. This tutorial will guide you through the process of installing Coq on Windows, Mac, and Linux, and then how to write a simple proof using Coqtop REPL. If you come from Haskell, you can think of Coq like GHC and Coqtop like GHCi.

# Installing Coq

* Installing Coq on **Windows**

   - Download the Windows installer from the Coq website (https://coq.inria.fr/download).
   - Run the installer and follow the instructions. The installer will guide you through the process and install Coq and CoqIDE (the integrated development environment for Coq).

* Installing Coq on **Mac**

   - The easiest way to install Coq on Mac is through Homebrew.
   - You can install Coq by running: `brew install coq`.

* Installing Coq on **Linux**

   - For Debian-based distributions like Ubuntu, you can install Coq using apt. Run the following commands in your terminal:
     {% vimhl bash %}
     sudo apt install coq
     {% endvimhl %}
   - For Red Hat-based distributions like Fedora, you can install Coq using dnf:
     {% vimhl bash %}
     sudo dnf install coq
     {% endvimhl %}
   - For Arch Linux-based distributions like Manjaro, you can install Coq using pacman:
     {% vimhl bash %}
     sudo pacman -S coq
     {% endvimhl %}

# Writing a Simple Proof with Coqtop

<!-- If you wish to paste or write a proof without utilizing an interactive REPL, you can insert your code into a file, such as `hello_world.v`, and execute it using the command `coqc hello_world.v`. If your proofs are accurate, this command will exit with 0; otherwise, it will provide an error explaining why the proof is not yet complete. -->

Now, we aim to prove that 1 + 1 = 2 using Coq. Let's create a file named `hello_proof.v` and insert the following proposition that we seek to prove:

{% vimhl v %}
Proposition one_plus_one_is_two : 1 + 1 = 2.
{% endvimhl %}

If we just try to compile our proof with `coqc hello_proof.v` it will throw the following error as epexteced:

```
Error: There are pending proofs in file ./hello_proof.v: one_plus_one_is_two.
```

That is because we have an unproven statement in our file. Now lets load our file into `coqtop` with `coqtop -load-vernac-source hello_proof.v` and try to prove this trivial proposition interactivly.


Coqtop is the Read-Eval-Print Loop (REPL) for Coq. It allows you to interactively develop proofs. Here's how to write a simple proof using Coqtop.

1. Start Coqtop by running `coqtop` in your terminal.

2. Let's prove that for all natural numbers, if n is greater than or equal to 0, then n + 0 = n. In Coq, we can write this as follows:

     {% vimhl v %}
Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
simpl. rewrite -> IHn'. reflexivity.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'.reflexivity. Qed.

Proposition one_equals_one : 1 = 1.
Proof.
reflexivity.
Qed.



<!-- Print lt. -->
<!-- lt = fun n m : nat => S n <= m -->
     <!-- : nat -> nat -> Prop -->
Proposition zero_lt_three : 0 < 3.
Proof.
unfold lt.
repeat constructor.
Qed.

Proposition one_plus_one_is_two : 1 + 1 = 2.
Proof.
simpl.
reflexivity.
Qed.

     {% endvimhl %}

   This statement hasn't been proven yet. It's just a theorem statement. To prove it, we need to enter proof mode by typing `Proof.`

3. Now we're in proof mode. The goal is to show that `n + 0 = n` for any natural number `n`. We can start by introducing `n`:

   ```
   intros n.
   ```

   This moves `n` from our assumptions to our context.

4. Now we need to prove that `n + 0 = n`. In Coq, natural numbers are defined inductively, and `0` is the base case. So we can prove this by induction on `n`:

   ```
   induction n as [| n' IHn'].
   ```

   This breaks our proof into two cases. The first case is when `n` is `0`, and the second case is when `n` is the successor of some number `n'`.

5. In the base case, we need to prove that `0 + 0 = 0`. This is true by the definition of `+`, so we can use the `reflexivity` tactic:

   ```
   reflexivity.
   ```

6. In the inductive case, we need to prove that `(S n') + 0 = S n'`. By the definition of `+`, this simplifies to `S (n' + 0) = S n'`. By our inductive hypothesis, `n' + 0 = n'`, so we can use the `rewrite` tactic to simplify our goal:

   ```
   rewrite -> IHn'.
   reflexivity.
   ```

7. Now we've proven both cases, so our proof is complete. We can end the proof with `Qed.`

Conclusion

Congratulations! You've installed Coq and written a simple proof using Coqtop REPL. Coq is a powerful tool for formalizing mathematical proofs and programming language semantics, and there's much more to learn. Happy proving!
