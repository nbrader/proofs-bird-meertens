#!/bin/bash

# Script to list all completed proofs (those ending in Qed) from BirdMeertens project

echo "# COMPLETED THEOREMS AND LEMMAS IN BIRDMEERTENS PROJECT"
echo ""
echo "Generated on: $(date)"
echo ""

cd "Coq/BirdMeertens"

for file in BirdMeertens.v Lemmas.v ListFunctions.v ProofStrategy.v FunctionLemmas.v; do
    echo "## $file"
    # Find theorems/lemmas that end with Qed
    completed_proofs=$(grep -B10 "^Qed\.$" "$file" | grep -E "^(Theorem|Lemma|Example)" | sed 's/:.*$//' | sed 's/^/- /')
    
    if [ -n "$completed_proofs" ]; then
        echo "$completed_proofs"
    else
        echo "No completed proofs found"
    fi
    echo ""
done

echo ""
echo "## Summary"
total_qed=$(find . -name "*.v" -exec grep -c "^Qed\.$" {} + | paste -sd+ | bc)
total_admitted=$(find . -name "*.v" -exec grep -c "^Admitted\.$" {} + | paste -sd+ | bc)

echo "- Total completed proofs (Qed): $total_qed"
echo "- Total admitted proofs: $total_admitted"
echo "- Completion rate: $(echo "scale=1; $total_qed * 100 / ($total_qed + $total_admitted)" | bc)%"