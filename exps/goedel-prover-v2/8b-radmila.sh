
./generate-with-vllm.py \
    --model Goedel-LM/Goedel-Prover-V2-8B \
    --dataset data/lean-ineq-radmila.json \
    --prompt_template prove \
    --n 4 \
    --output ${0%.*}.json
