#!/usr/bin/env python3

import argparse
import json
from vllm import LLM, SamplingParams

import prompts


def generate(args):
    with open(args.dataset) as f:
        statements = json.load(f)
    prompt_template = getattr(prompts, args.prompt_template)
    input_prompts = [prompt_template.format(x=s) for s in statements]
    print(f"Initializing with model {args.model} and {args.tokenizer}")
    model = LLM(
        model=args.model,
        tokenizer=args.tokenizer,
        gpu_memory_utilization=args.gpu_memory_utilization,
        swap_space=args.swap_space,
    )
    sampling_params = SamplingParams(
        n=args.n,
        temperature=args.temperature,
        max_tokens=16384,
        skip_special_tokens=True,
        include_stop_str_in_output=False,
    )
    outputs = model.generate(input_prompts, sampling_params)
    #passes = []
    for output, statement in zip(outputs, statements):
        responses = [o.text for o in output.outputs]
        #final_answers = [extract_final_answer(o) for o in responses]
        final_answers = responses
        #correct = []
        print(f'INPUT STATEMENT: {statement}')
        for a in final_answers:
            print(f'CANDIDATE PROOF: {a}')
            #correct.append(evaluate(statement, a))
        #passed = sum(correct) > 0
        #print(f'PASS: {passed}')
        print('END OF CANDIDATES')
        print('-' * 80, flush=True)
        #passes.append(passed)
    #pass_rate = sum(passes) / len(passes)
    print('DONE')
    #print(f'PASS RATE: {sum(passes)} / {len(passes)} = {pass_rate}')


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=str)
    parser.add_argument("--tokenizer", type=str)
    parser.add_argument("--dataset", type=str)
    parser.add_argument("--prompt_template", type=str)
    parser.add_argument("--n", type=int, default=1)
    parser.add_argument("--temperature", type=float, default=1.0)
    parser.add_argument("--gpu_memory_utilization", type=float, default=0.9)
    parser.add_argument("--swap_space", type=float, default=4)
    args = parser.parse_args()
    if args.tokenizer is None:
        args.tokenizer = args.model
    #log_args(args)
    generate(args)
