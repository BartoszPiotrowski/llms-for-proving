
./generate-with-vllm.py \
    --model Goedel-LM/Goedel-Prover-V2-32B \
    --dataset data/lean-ineq-zcve.json \
    --prompt_template prove \
    --n 16 \
    --output ${0%.*}.json
