#!/usr/bin/env python3

# import os
import re
import sys
# import shutil
import subprocess
# from itertools import product
# from collections import deque
import heapq
import argparse

# 1. Setup command-line argument parser
parser = argparse.ArgumentParser(description="Simplify a mathematical term using Twee or a substitution file.")

# Add -s first, as it changes the requirements
parser.add_argument("-s", "--substitution-file", 
                    help="A file containing pre-computed substitutions. If given, rule_file and term args are ignored.")

parser.add_argument("rule_file", nargs='?', default=None, 
                    help="The .p file containing the rewrite rules (required if -s is not used).")

term_group = parser.add_mutually_exclusive_group(required=False)
term_group.add_argument("-T", "--term", 
                        help="The term string to simplify (required if -s is not used).")
term_group.add_argument("-F", "--term-file", 
                        help="A file containing the term string to simplify (required if -s is not used).")

parser.add_argument("-t", "--timeout", default="1", 
                    help="Timeout for the Twee prover (default: 1 second, ignored if -s is used).")
parser.add_argument("-f", "--no-flatten", action="store_false",
                    help="Prevents flattening nested functions in the goal term (ignored if -s is used).")

args = parser.parse_args()

# --- Validation ---
if not args.substitution_file:
    # If -s is NOT given, the old arguments are required.
    if not args.rule_file:
        parser.error("argument 'rule_file' is required (or use -s)")
    if not args.term and not args.term_file:
        parser.error("one of the arguments -T/--term or -F/--term-file is required (or use -s)")
# ------------------


class Formula:
    def __init__(self, id, args):
        self.id = id
        self.args = args
        self.is_var = False
        self.value = None
        if len(args) == 0:
            if id.lower().startswith("numneg") or id.lower().startswith("negnum"):
                self.value = -int(id[6:])
            elif id.lower().startswith("num"):
                self.value = int(id[3:])
            elif id == id.upper():
                self.is_var = True
            # else:
            #     raise Exception(f"unknown constant: {id}")
        
    def __repr__(self):
        if len(self.args) == 0:
            return self.id
        else:
            return f"{self.id}({','.join(map(str, self.args))})"
        
    def __eq__(self, other):
        if not isinstance(other, Formula):
            return False
        return self.id == other.id and self.args == other.args
    
    def __hash__(self):
        return hash((self.id, tuple(self.args)))
        

def parse_formula(s):
    s = s.replace(" ","")
    word = ""
    while s!="" and s[0] not in ['(',')',',']:
        word += s[0]
        s = s[1:]
    if s == "":
        return Formula(word, []), s
    if s[0] == '(':
        s = s[1:]
        args = []
        while True:
            if s[0] == ')':
                s = s[1:]
                break
            else:
                arg, s = parse_formula(s)
                args.append(arg)
                if s[0] == ',':
                    s = s[1:]
        return Formula(word, args), s
    else:
        return Formula(word, []), s

def collect_subterms(t, idx):
    if idx > 0 and len(t.args) == 0:
        return idx, t.id
    current_idx = idx+1
    new_args = []
    for arg in t.args:
        current_idx, subterm = collect_subterms(arg, current_idx)
        new_args.append(subterm)
    name = f"goal{idx}"
    subterm = Formula(t.id, new_args)
    goals.append(f'cnf(goal,axiom, {name} = {subterm}).')
    return current_idx, name

def replace(term_str, old, new):
    term,rest = parse_formula(term_str)
    assert rest == ""
    new_term,rest = parse_formula(new)
    assert rest == ""
    def replace_rec(t):
        if t.id == old and len(t.args) == 0:
            return new_term
        else:
            new_args = [replace_rec(arg) for arg in t.args]
            return Formula(t.id, new_args)
    replaced = replace_rec(term)
    return str(replaced)

# -----------------------------------------------------------------
# Main script logic
# -----------------------------------------------------------------

subst_set = []
pattern = re.compile(r'goal\d+')

if args.substitution_file:
    # --- PATH 1: Load substitutions from file ---
    print(f"Loading substitutions from {args.substitution_file}...")
    try:
        with open(args.substitution_file, 'r') as f:
            lines = f.readlines()
            # skip all lines until we find a line starting with "Substitutions found:"
            # end at line Resolving
            start_idx = 0
            end_idx = len(lines)
            for i, line in enumerate(lines):
                if line.startswith("Substitutions found:"):
                    start_idx = i + 1
                if line.startswith("Resolving"):
                    end_idx = i
                    break
            lines = lines[start_idx:end_idx]
            for line in lines:
                line = line.strip()
                if not line:
                    continue
                
                # Parse the "lhs -> rhs" or "lhs <-> rhs" format
                if "<->" in line:
                    lhs, rhs = line.split(" <-> ")
                elif "->" in line:
                    lhs, rhs = line.split(" -> ")
                else:
                    print(f"Warning: Skipping malformed line in substitution file: {line}", file=sys.stderr)
                    continue
                
                lhs = lhs.strip()
                rhs = rhs.strip()
                
                if lhs == rhs:
                    continue
                
                # only add if one side is pattern goal\d+
                if pattern.match(lhs) or pattern.match(rhs):
                    subst_set.append((lhs, rhs))
                else:
                    print(f"Warning: Skipping line (no goal pattern): {line}", file=sys.stderr)

    except FileNotFoundError:
        print(f"Error: Substitution file not found: {args.substitution_file}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error reading substitution file: {e}", file=sys.stderr)
        sys.exit(1)

else:
    # --- PATH 2: Original logic, run Twee ---

    # 2. Get the rule file and timeout from parsed args
    rule_file = args.rule_file
    timeout = args.timeout
    flatten = args.no_flatten

    # 3. Get the term string from either --term or --term-file
    term_string = ""
    if args.term:
        term_string = args.term
    else: # args.term_file must be set
        try:
            with open(args.term_file, 'r') as f:
                term_string = f.read().strip()
        except FileNotFoundError:
            print(f"Error: Term file not found: {args.term_file}", file=sys.stderr)
            sys.exit(1)
        except Exception as e:
            print(f"Error reading term file: {e}", file=sys.stderr)
            sys.exit(1)

    if not term_string:
        print("Error: No term provided or term file was empty.", file=sys.stderr)
        sys.exit(1)

    term,rest = parse_formula(term_string)
    if rest != "":
        raise Exception("parsing error")

    with open(rule_file, "r") as f:
        data = f.read()

    goals = []

    if flatten:
        collect_subterms(term, 0)
    else:
        goals.append('cnf(goal,axiom, goal0 = '+str(term)+').')

    goals.append('cnf(goal,conjecture, zero = one).')
    print("Generated goals:")
    for g in goals:
        print(" ", g)
    # sys.exit(0)

    data += "\n"+"\n".join(goals) + "\n"

    # print(data)

    # run twee.sh with data as input
    print(f"Running Twee with timeout={timeout}s...")
    proc = subprocess.Popen(["./twee.sh", str(timeout), "-"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate(input=data.encode())

    output = out.decode()
    
    if True:
        limiter="Goal 1 (goal): zero = one."
        if limiter not in output:
            print("Error: Could not find Twee output limiter. Twee may have failed.", file=sys.stderr)
            print("\n--- Twee stdout: ---", file=sys.stderr)
            print(out.decode(), file=sys.stderr)
            print("\n--- Twee stderr: ---", file=sys.stderr)
            print(err.decode(), file=sys.stderr)
            sys.exit(1)
            
        output = output.split(limiter)[1]
        
    lines = output.split("\n")
    # lines = [line for line in lines if "goal" in line]
    # subst_set = {}
    
    for line in lines:
        # print(line)
        # if "->" not in line:
        #     continue
        if "goal" not in line:
            continue
        # remove "\d+\. " at start of line
        line = re.sub(r"^\s*\d+\.\s+", "", line)
        if "<->" in line:
            lhs, rhs = line.split(" <-> ")
        elif "->" in line:
            lhs, rhs = line.split(" -> ")
        else:
            continue
        
        lhs = lhs.strip()
        rhs = rhs.strip()
        if lhs == rhs:
            continue
        # only add if one side is pattern goal\d+
        if re.match(r'goal\d+', lhs) or re.match(r'goal\d+', rhs):
            subst_set.append((lhs, rhs))
    
# -----------------------------------------------------------------
# Resolver logic (common to both paths)
# -----------------------------------------------------------------
    
print("\nSubstitutions found:")
for lhs, rhs in subst_set:
    print(f"  {lhs} -> {rhs}")

# we have for each goal one or multiple substitutions (potentially just other goal)
# we want to find a order (starting at goal0) to resolve these substitutions to reach a final term
# without any remaining goals

# inverse topo sort + dijkstra:
# start with leaf nodes in priorityqueue (sorted by size)
# replace in all other nodes, continue

queue = []
subst = {}
remaining = set()
for lhs, rhs in subst_set:
    if not pattern.search(rhs):
        heapq.heappush(queue, (len(rhs), lhs, rhs))
    elif not pattern.search(lhs):
        heapq.heappush(queue, (len(lhs), rhs, lhs))
    else:
        remaining.add((lhs, rhs))
        
while queue:
    _, g, t = heapq.heappop(queue)
    if g in subst:
        # we already found a smaller term for this goal
        continue
    print(f"Resolving {g} -> {t}")
    subst[g] = t
    new_remaining = set()
    for lhs, rhs in remaining:
        if lhs == g or rhs == g:
            # we already found a smaller term for this goal
            continue
        # new_lhs = lhs.replace(g, t)
        # new_rhs = rhs.replace(g, t)
        new_lhs = replace(lhs, g, t)
        new_rhs = replace(rhs, g, t)
        # if (lhs != new_lhs or rhs != new_rhs) and (g == "goal80"):
        #     print(f"  Updated: {lhs} -> {rhs}  to  {new_lhs} -> {new_rhs}")
        if not pattern.search(new_rhs):
            heapq.heappush(queue, (len(new_rhs), new_lhs, new_rhs))
        elif not pattern.search(new_lhs):
            heapq.heappush(queue, (len(new_lhs), new_rhs, new_lhs))
        else:
            new_remaining.add((new_lhs, new_rhs))
    remaining = new_remaining
            
print("\nFinal substitutions:")
for lhs, rhs in subst.items():
    print(f"  {lhs} -> {rhs}")

print("\nResolved term for goal0:")
if "goal0" in subst:
    print(subst["goal0"])
else:
    print("Error: Could not resolve goal0.")
    if not args.substitution_file and "goal0" not in [l for l,r in subst_set] + [r for l,r in subst_set]:
         print("Note: 'goal0' was not found in Twee output.")
    elif not subst_set:
         print("Note: No substitutions were found or provided.")
    else:
         print("Note: Resolution may have failed or goal0 was not in the set.")
         print("Best effort result:")
         goals = []
         for lhs, rhs in remaining:
             if lhs == "goal0":
                goals.append(rhs)
             elif rhs == "goal0":
                goals.append(lhs)
                #  print(f"  {lhs} -> {rhs}")
         if goals:
            print(min(goals, key=len))