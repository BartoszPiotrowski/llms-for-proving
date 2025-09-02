
./generate-with-vllm.py \
    --model Goedel-LM/Goedel-Prover-V2-32B \
    --dataset data/lean-ineq-book567.json \
    --prompt_template prove \
    --n 16 \
    --data_parallel_size 4 \
    --output ${0%.*}.json
