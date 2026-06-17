#!/usr/bin/env bash
# run_examples.sh — run all .metta files in examples/, with optional skip list
#
# Usage:
#   ./run_examples.sh                          # run all
#   ./run_examples.sh --skip fib greedy_chess  # skip files matching these names
#   ./run_examples.sh --skip fib --skip python # same, one at a time

set -euo pipefail

EXAMPLES_DIR="$(dirname "$0")/examples"
BINARY="../target/release/mork-metta"

SKIP=()

# Parse args: --skip <name> [<name> ...] (repeat as needed)
while [[ $# -gt 0 ]]; do
	case "$1" in
	--skip | -s)
		shift
		while [[ $# -gt 0 && "$1" != --* ]]; do
			SKIP+=("$1")
			shift
		done
		;;
	*)
		echo "Unknown argument: $1" >&2
		echo "Usage: $0 [--skip name1 name2 ...]" >&2
		exit 1
		;;
	esac
done

should_skip() {
	local file="$1"
	local base
	base="$(basename "$file" .metta)"
	for pattern in "${SKIP[@]}"; do
		if [[ "$base" == *"$pattern"* ]]; then
			return 0
		fi
	done
	return 1
}

PASS=0
FAIL=0
SKIPPED=0
FAILED_FILES=()

for metta_file in "$EXAMPLES_DIR"/*.metta; do
	[[ -f "$metta_file" ]] || continue

	if should_skip "$metta_file"; then
		echo "SKIP  $(basename "$metta_file")"
		((SKIPPED++)) || true
		continue
	fi

	printf "RUN   %-50s" "$(basename "$metta_file")"
	if output=$($BINARY "$metta_file" 2>&1); then
		if grep -q "❌" <<<"$output"; then
			echo "FAIL"
			echo "$output" | sed -n '/❌/p' | sed 's/^/      /'
			FAILED_FILES+=("$(basename "$metta_file")")
			((FAIL++)) || true
		else
			echo "ok"
			((PASS++)) || true
		fi
	else
		echo "FAIL"
		echo "      $output" | head -5
		FAILED_FILES+=("$(basename "$metta_file")")
		((FAIL++)) || true
	fi

done

echo ""
echo "Results: $PASS passed, $FAIL failed, $SKIPPED skipped"

if [[ ${#FAILED_FILES[@]} -gt 0 ]]; then
	echo "Failed:"
	for f in "${FAILED_FILES[@]}"; do
		echo "  - $f"
	done
	exit 1
fi
