#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
# Lint for the counted decision procedure (lean/ZZN/Timed/*.lean, except TimeM.lean and the files of
# proofs). Inside every `def` body of Catalogue.lean, Thin.lean, Main.lean, ThinWit.lean, Band.lean, Lift.lean,
# Solve.lean and Construct.lean, only the counted
# operations of TimeM.lean and constant-time functions may appear. Rejected:
#  * list operations that are not counted wrappers (map, filter, any, all, find?, length, ...);
#  * `++` (except in the allow-listed constant-size helpers below);
#  * membership tests;
#  * any call to an uncounted function of the original algorithm.
# Exit status 1 and a report on any violation.
import re, sys, os
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ZZN', 'Timed')
FILES = ['Catalogue.lean', 'Thin.lean', 'Main.lean', 'ThinWit.lean', 'Band.lean', 'Lift.lean', 'Solve.lean',
         'Construct.lean']
# Constant-size helpers: lists of at most five elements, built or matched directly.
ALLOW = {'endsL', 'optsL', 'cornersL', 'optSnd', 'Q', 'Nst', 'Kst', 'Cdec', 'stepCellFrom',
         # `++` charged by hand: `gap` has at most two cells (cost 3); `X ++ _` is charged `|X| + 1`.
         'stretchT', 'insBT'}
TOKENS = [r'∈', r'∉', r'∑', r'\+\+',
  r'\.(filter|map|all|any|find\?|length|foldl|foldr|flatMap|filterMap|erase|contains|zip|zipIdx|'
  r'reverse|dedup|sum|modify|findIdx\?|range|insert|append)\b',
  r'\b(List|Finset|Array)\.']
UNCOUNTED = '''View.at View.empty makeView parityOk sortByKey t1Fires t2Fires l1Fires l6Closures l6Fires
  testL2 testL3 testL4 testL5 edgeClosure sameSet corner4 boundaryOnly frameFires rewritesAt moveFirst
  rwStep rewriteAll notchLen staircase stairOf walk3 positions effAlt3 effAlt fires fires2 fires3
  stepCell closeP insSorted normS msortS mergeS splitS dedupAdj stage stageF inside insideF dpAccept
  dpAcceptF thinB thinBF solvableB noExit termAt outerWalk outerFaceWalk effectiveAlternation
  thinSolveW solveDP insideW stageW stepCellW stepCellG closeOuts closeWit segNew dropKeys lookD orientS
  orientN orientP dedupKey dedupKeyAux restK puOf plOf stretch insB spliceE absorbE flipE sweepLeftE
  sweepRightE bandFrom bandExtE cond1 seedAt freeLineB endBelowB endAboveB redB findRed liftE solB
  chainAdjacent checkE solveRec solveZ solveZZN'''.split()
TOP = re.compile(r'^(def|lemma|theorem|@\[|section|end|namespace|open|variable|include|instance|'
                 r'/-|--|private|noncomputable|abbrev|structure|omit|set_option|#)')
def strip_comments(t):
  t = re.sub(r'/-.*?-/', '', t, flags=re.S)
  return re.sub(r'--.*', '', t)
bad = 0
for name in FILES:
  fn = os.path.join(ROOT, name)
  lines = strip_comments(open(fn).read()).split('\n')
  i = 0
  while i < len(lines):
    if re.match(r'^(private )?def ', lines[i]):
      j = i + 1
      while j < len(lines) and not (lines[j] and TOP.match(lines[j])): j += 1
      body = '\n'.join(lines[i:j])
      head = re.match(r'^(?:private )?def\s+(\S+)', lines[i]).group(1)
      cut = body.find(':=')
      code = body[cut:] if cut >= 0 else body
      if head not in ALLOW:
        # `st.any` is the Boolean field of a rewrite state, not `List.any`.
        code = code.replace('st.any', 'st_anyField')
        for ln in code.split('\n'):
          for tok in TOKENS:
            if re.search(tok, ln):
              print(f'{name}: {head}: uncounted operation /{tok}/ in: {ln.strip()}'); bad += 1
          for nm in UNCOUNTED:
            if re.search(r'(?<![\w\'.])' + re.escape(nm) + r'(?![\w\'])', ln):
              print(f'{name}: {head}: uncounted function {nm} in: {ln.strip()}'); bad += 1
      i = j
    else:
      i += 1
print('timed_lint:', 'OK' if bad == 0 else f'{bad} violation(s)')
sys.exit(1 if bad else 0)
