
./generate-with-vllm.py \
    --model Goedel-LM/Goedel-Prover-V2-8B \
    --dataset data/proofnet/all-prep.jsonl \
    --prompt_template prove \
    --n 32 \
    --output ${0%.*}.json
