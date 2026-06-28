import re

def extract_calls(text):
    theorem_map = {}

    # Find:
    # let b : ... := axiom_innertransitivity
    theorem_defs = re.finditer(
        r'let\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*:[\s\S]*?:=\s*\n\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*\n\s*in',
        text
    )

    for m in theorem_defs:
        theorem_map[m.group(1)] = m.group(2)

    calls = []

    lines = text.splitlines()

    for line in lines:
        line = line.strip()

        for var, theorem in theorem_map.items():
            if re.match(rf'^{var}\s+', line):
                args = line[len(var):].strip()
                calls.append(f"{theorem} {args}")

    return calls


with open("proof.txt") as f:
    proof = f.read()

for c in extract_calls(proof):
    print(c)
print("FILE LOADED")
print(proof[:500])

calls = extract_calls(proof)

print("CALLS FOUND:", len(calls))

for c in calls:
    print(c)
