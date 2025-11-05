#!/bin/bash
# Generate clean bundle with only active Lean files

OUTPUT="all_Lean_CLEAN_$(date +%Y%m%d_%H%M%S).txt"

for f in Metamath/*.lean; do
  echo ""
  echo "\$( $(basename "$f") \$)"
  cat "$f"
done > "$OUTPUT"

echo "Created $OUTPUT"
ls -lh "$OUTPUT"
