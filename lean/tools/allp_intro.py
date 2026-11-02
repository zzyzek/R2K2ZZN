#!/usr/bin/env python3
"""Rewrite `intro p hp; simp only [...] at hp; rcases ...; exacts [...]` membership proofs in
generated WinKU modules into one `AllP.mem` term (see tools/WinGenU.lean, memIntro), and add
the AllP definitions to Shared/Main.lean.

usage: allp_intro.py FILE...
"""
import re, sys

ALLP = '''def AllP {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | a :: l => P a ∧ AllP P l
theorem AllP.mem {α : Type} {P : α → Prop} : ∀ {L : List α}, AllP P L → ∀ p ∈ L, P p
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, t⟩, p, .tail _ hp => AllP.mem t p hp
'''
MANY = re.compile(r'  intro p hp\n  simp only \[(\w+), List\.mem_cons, List\.mem_nil_iff, or_false\] at hp\n'
                  r'  rcases hp with [rfl| ]+\n  exacts \[(.*)\]\n')
ONE = re.compile(r'  intro p hp\n  simp only \[(\w+), List\.mem_cons, List\.mem_nil_iff, or_false\] at hp\n'
                 r'  subst hp; exact (.*)\n')
NONE = re.compile(r'  intro p hp\n  simp \[(\w+)\] at hp\n')

for f in sys.argv[1:]:
    s = open(f).read()
    s, a = MANY.subn(lambda m: f'  exact AllP.mem (L := {m[1]}) ⟨{m[2]}, trivial⟩\n', s)
    s, b = ONE.subn(lambda m: f'  exact AllP.mem (L := {m[1]}) ⟨{m[2]}, trivial⟩\n', s)
    s, c = NONE.subn(lambda m: f'  exact AllP.mem (L := {m[1]}) trivial\n', s)
    if f.endswith('Shared/Main.lean') and 'def AllP' not in s:
        s = s.replace('open ZZN.WinK ZZN.Win\n', 'open ZZN.WinK ZZN.Win\n' + ALLP, 1)
    open(f, 'w').write(s)
    print(f, a, b, c)
