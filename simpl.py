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
parser = argparse.ArgumentParser(description="Simplify a mathematical term using Twee.")
parser.add_argument("rule_file", help="The .p file containing the rewrite rules.")

term_group = parser.add_mutually_exclusive_group(required=True)
term_group.add_argument("-T", "--term", help="The term string to simplify.")
term_group.add_argument("-F", "--term-file", help="A file containing the term string to simplify.")

parser.add_argument("-t", "--timeout", default="1", 
                    help="Timeout for the Twee prover (default: 1 second).")
parser.add_argument("-f", "--no-flatten", action="store_false",
                    help="Prevents flattening nested functions in the goal term.")

args = parser.parse_args()

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


# rule_file = "math_term3.p"
# term = "mul(b, add(zero, mul(x, add(add(add(mul(x, one), sub(pow(y, zero), div(mul(zero, z), pow(a, one)))), div(pow(pow(b, one), one), mul(one, one))), div(mul(d, zero), pow(e, one))))))"
term,rest = parse_formula(term_string)
if rest != "":
    raise Exception("parsing error")

with open(rule_file, "r") as f:
    data = f.read()

goals = []

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
proc = subprocess.Popen(["./twee.sh", str(timeout), "-"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
out, err = proc.communicate(input=data.encode())

output = out.decode()
limiter="Gave up on reaching the given resource limit"
if limiter in output:
    output = output.split(limiter)[1]
else:
    limiter="Goal 1 (goal): zero = one."
    output = output.split(limiter)[1]
lines = output.split("\n")
# lines = [line for line in lines if "goal" in line]
# subst_set = {}
subst_set = []
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
    
# remove if no base (not either side a variable)
# subst_set = [(lhs, rhs) for lhs, rhs in subst_set if "(" not in lhs or "(" not in rhs]

pattern = re.compile(r'goal\d+')
    
print("Substitutions found:")
for lhs, rhs in subst_set:
    print(f"{lhs} -> {rhs}")

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
        
while queue:
    _, g, t = heapq.heappop(queue)
    print(f"Resolving {g} -> {t}")
    if g in subst:
        # we already found a smaller term for this goal
        continue
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
print(subst["goal0"])
