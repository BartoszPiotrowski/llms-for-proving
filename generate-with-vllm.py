#!/usr/bin/env python3

import argparse
import json
from vllm import LLM, SamplingParams

import prompts
from utils import extract_proof, log_args


def generate(args):
    examples = [json.loads(l) for l in open(args.dataset)]
    statements = [e['statement'] for e in examples]
    ids = [e['id'] for e in examples]
    prompt_template = getattr(prompts, args.prompt_template)
    input_prompts = [prompt_template.format(x=s) for s in statements]
    print(f"Initializing with model {args.model} and {args.tokenizer}")
    model = LLM(
        model=args.model,
        tokenizer=args.tokenizer,
        gpu_memory_utilization=args.gpu_memory_utilization,
        swap_space=args.swap_space,
        max_model_len=args.max_model_len,
        data_parallel_size=args.data_parallel_size,
    )
    sampling_params = SamplingParams(
        n=args.n,
        temperature=args.temperature,
        max_tokens=16384,
        skip_special_tokens=True,
        include_stop_str_in_output=False,
    )
    outputs = model.generate(input_prompts, sampling_params)
    proof_dicts = []
    for id, output, statement in zip(ids, outputs, statements):
        responses = [o.text for o in output.outputs]
        proofs = [extract_proof(r) for r in responses]
        proof_dicts.append({'id': id, 'statement': statement, 'proofs': proofs})
    with open(args.output, 'w') as f:
        json.dump(proof_dicts, f)
    print('DONE')


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=str)
    parser.add_argument("--tokenizer", type=str)
    parser.add_argument("--dataset", type=str)
    parser.add_argument("--prompt_template", type=str)
    parser.add_argument("--n", type=int, default=1)
    parser.add_argument("--temperature", type=float, default=1.0)
    parser.add_argument("--gpu_memory_utilization", type=float, default=0.9)
    parser.add_argument("--max_model_len", type=int, default=30000)
    parser.add_argument("--data_parallel_size", type=int, default=1)
    parser.add_argument("--swap_space", type=float, default=4)
    parser.add_argument("--output", type=str)
    args = parser.parse_args()
    if args.tokenizer is None:
        args.tokenizer = args.model
    log_args(args)
    generate(args)
