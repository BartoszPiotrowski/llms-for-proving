
./generate-with-vllm.py \
    --model Goedel-LM/Goedel-Prover-V2-8B \
    --dataset data/lean-ineq-kiran.json \
    --prompt_template prove \
    --n 16 \
    --output ${0%.*}.json
