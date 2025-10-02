import json
import hashlib
import tempfile
import subprocess
import os
import re
import sys


def log_args(args):
    args = vars(args)
    for a in args:
        print(f'ARGUMENT: {a}={args[a]}')

# the lean_eval function copied from Alex Gu
def lean_eval(code_snippet, lean_dir, use_cache=True):
    cache_dir = os.path.join(lean_dir, ".cache")
    os.makedirs(cache_dir, exist_ok=True)

    # Hash the code snippet to use as cache key
    code_hash = hashlib.sha256(code_snippet.encode("utf-8")).hexdigest()
    cache_file = os.path.join(cache_dir, f"{code_hash}.json")

    # Check cache
    if use_cache and os.path.exists(cache_file):
        with open(cache_file, "r") as f:
            cached = json.load(f)
        return cached["success"], cached["stdout"], cached["stderr"]

    # Not cached: run the check
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", delete=False, dir=cache_dir
    ) as temp_file:
        temp_file.write(code_snippet)
        temp_file.flush()

    try:
        result = subprocess.run(
            ["lake", "env", "lean", temp_file.name],
            capture_output=True,
            text=True,
            timeout=300,
            cwd=lean_dir,
        )
        success = result.returncode == 0
        stdout = result.stdout.strip()
        stderr = result.stderr.strip()
    except Exception as e:
        success = False
        stdout = ""
        stderr = str(e)
    finally:
        os.unlink(os.path.join(cache_dir, temp_file.name))

    # Cache the result
    with open(cache_file, "w") as f:
        print(f"Caching the result to {cache_file}", file=sys.stderr)
        json.dump({"success": success, "stdout": stdout, "stderr": stderr}, f)

    return success, stdout, stderr


def erase(long, short):
    long, short = list(long), list(short)
    whitespace = {" ", "\n"}
    i, j = 0, 0
    while j < len(short):
        if long[i] == short[j]:
            long[i] = " "
            i += 1
            j += 1
        elif long[i] in whitespace:
            i += 1
        elif short[j] in whitespace:
            j += 1
        else:
            raise SyntaxError
    return "".join(long)

def remove_statement(statement_and_proof):
    if ":= by" in statement_and_proof:
        return statement_and_proof.split(":= by", maxsplit=1)[1].strip()
    return statement_and_proof.split(":=", maxsplit=1)[1].strip()

def remove_comments(proof):
    return re.sub(" +--.*", "", proof)

def extract_proof(llm_output):
    code_delimiters = re.findall(r'```', llm_output)
    if len(code_delimiters) < 2:
        return ''
    proof = []
    in_proof = False
    for l in reversed(llm_output.splitlines()):
        if '```' in l and in_proof:
            break
        if in_proof:
            proof.append(l)
        if '```' in l:
            in_proof = True
    return '\n'.join(reversed(proof)).strip()

imports='''
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
'''

def preprocess_proof(proof):
    if not proof or re.search(r'\bsorry\b', proof):
        return None
    return '\n'.join([imports, proof])

def chunk(l, chunk_size):
    chunks = []
    while len(l) > chunk_size:
        c, r = l[:chunk_size], l[chunk_size:]
        chunks.append(c)
        l = r
    if len(l) > int(chunk_size / 3):
        chunks.append(l)
    else:
        chunks[-1].extend(l)
    return chunks



if __name__ == "__main__":

    lean_snippet = """
import Mathlib

theorem problem_1 (a b : ℕ)
(ha : 10 ≤ a ∧ a < 100)
(hab : a * b = 161) :
(10 * (a % 10) + (a / 10)) * b = 224 := by {
set dv := ({1, 7, 23, 161} : Finset ℕ)
have h1: a ∈ Nat.divisors 161 := by {simp; rw [← hab]; simp}
have h2: a ∈ dv := by exact h1
have h3: a = 23 := by aesop
rw [h3] at hab
have h4: b = 7 := by linarith [h3, hab]
rw [h3, h4]
<;> linarith <;>
omega
<;> rw [h3]
<;> linarith
}
"""
    print("Testing the following Lean snippet...\n")
    print("-" * 50)
    print(lean_snippet)
    print("-" * 50)
    lean_dir = "/Users/bpio/Research/Code/Bartosz/mathlib-4-20"
    success, output, error = lean_eval(lean_snippet, lean_dir)
    print(f"Success: {success}")
    print(f"Output message:\n{output}")
    print(f"Error message:\n{error}")
