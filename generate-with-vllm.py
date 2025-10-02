#!/usr/bin/env python3

import argparse
import json
from vllm import LLM, SamplingParams

import prompts
from utils import extract_proof, log_args, chunk


def generate(args):
    print(f"Loading emxamples from {args.dataset}...")
    examples = [json.loads(l) for l in open(args.dataset)]
    prompt_template = getattr(prompts, args.prompt_template)
    print(f"Initializing with model {args.model} and {args.tokenizer}...")
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
    example_chunks = chunk(examples, args.chunk_size)
    with open(args.output, 'w') as f:
        for examples_chunk in example_chunks:
            statements = [e['statement'] for e in examples_chunk]
            input_prompts = [prompt_template.format(x=s) for s in statements]
            outputs = model.generate(input_prompts, sampling_params)
            for example, output in zip(examples_chunk, outputs):
                responses = [{'full_response': o.text,
                              'proof': extract_proof(o.text)} \
                                      for o in output.outputs]
                example['responses'] = responses
                f.write(json.dumps(example) + '\n')
    print('DONE')


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=str)
    parser.add_argument("--tokenizer", type=str)
    parser.add_argument("--dataset", type=str)
    parser.add_argument("--prompt_template", type=str)
    parser.add_argument("--n", type=int, default=1)
    parser.add_argument("--chunk_size", type=int, default=10)
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
