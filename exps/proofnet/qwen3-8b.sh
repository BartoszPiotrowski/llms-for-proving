
./generate-with-vllm.py \
    --model Qwen/Qwen3-8B \
    --dataset data/proofnet/all-prep.jsonl \
    --prompt_template prove \
    --n 4 \
    --chunk_size 10 \
    --output ${0%.*}.jsonl
