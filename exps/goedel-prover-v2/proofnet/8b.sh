
./generate-with-vllm.py \
    --model Goedel-LM/Goedel-Prover-V2-8B \
    --dataset data/proofnet/all-prep.jsonl \
    --prompt_template prove \
    --n 16 \
    --data_parallel_size 8 \
    --output ${0%.*}.json
