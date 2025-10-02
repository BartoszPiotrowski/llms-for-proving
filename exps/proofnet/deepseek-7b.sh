
./generate-with-vllm.py \
    --model deepseek-ai/DeepSeek-Prover-V2-7B \
    --dataset data/proofnet/all-prep.jsonl \
    --prompt_template prove \
    --n 32 \
    --output ${0%.*}.json
