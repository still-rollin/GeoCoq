def extract_calls(text):
    lines = [l.rstrip() for l in text.splitlines()]

    theorem = None
    calls = []

    for i, line in enumerate(lines):
        s = line.strip()

        # remember theorem names
        if s.startswith("axiom_") or s.startswith("lemma_"):
            theorem = s
            continue

        # find application line
        if theorem and s.startswith("b "):
            calls.append(f"{theorem} {s[2:]}")
            theorem = None

    return calls


with open("proof.txt") as f:
    proof = f.read()

calls = extract_calls(proof)

print("CALLS FOUND:", len(calls))
for c in calls:
    print(c)