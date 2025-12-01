#!/bin/bash
set -e

cd /home/pablo/projects/lean-csp/projects/CSP

echo "========================================================================"
echo "Symmetry Breaking Benchmark - Complete Pipeline"
echo "========================================================================"
echo ""

# Step 1: Generate instances by compiling proof files
echo "Step 1: Generating instances..."
echo "------------------------------------------------------------------------"

echo "  → Generating N-Queens instances..."
lake env lean --run CSP/L2S/Proofs/NQueensSB.lean

echo "  → Generating Graph Coloring instances..."
lake env lean --run CSP/L2S/Proofs/GraphColoringSB.lean

echo "  → Generating Latin Square instances..."
lake env lean --run CSP/L2S/Proofs/LatinSquareSB.lean

echo ""
echo "✓ Instances generated in CSP/L2S/Proofs/mzn/ and CSP/L2S/Proofs/smt2/"
echo ""

# Step 2: Run experiments
echo "Step 2: Running solvers..."
echo "------------------------------------------------------------------------"
python3 CSP/L2S/Proofs/Experiments/run_experiments.py

echo ""
echo "========================================================================"
echo "Complete! Check results in CSP/L2S/Proofs/Experiments/results/"
echo "========================================================================"
