
./generate-with-vllm.py \
    --model Goedel-LM/Goedel-Prover-V2-32B \
    --dataset data/proofnet/all-prep.jsonl \
    --prompt_template prove \
    --n 4 \
    --chunk_size 10 \
    --output ${0%.*}.jsonl
