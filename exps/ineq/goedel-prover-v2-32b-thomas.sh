
./generate-with-vllm.py \
    --model Goedel-LM/Goedel-Prover-V2-32B \
    --dataset data/lean-ineq-thomas.json \
    --prompt_template prove \
    --n 4 \
    --output ${0%.*}.json
