#!/bin/sh
# Live Oraqle demo (for the gradCapital call): extract kernel-resolved lemma
# applications from a GeoCoq proof of Euclid I (Elements lemma_3_7a).
# Requires: dune build theories/Elements/OriginalProofs/lemma_3_7a.vo  (done once)
cd "$(dirname "$0")" || exit 1
LEMMA="${1:-lemma_3_7a}"
python3 -c "
import sys; sys.path.insert(0, 'geolean_oracle')
from src.oracle import extract_resolved_calls
r = extract_resolved_calls('theories/Elements/OriginalProofs/${LEMMA}.v', '${LEMMA}')
print(f'=== {r.lemma_name}: kernel-resolved calls ===')
for c in r.resolved_calls:
    if c.name.startswith('lemma_'):
        print(f'{c.name:26s} ' + ' '.join(c.args))
"
