"""

** SPECIFICATION **

The file `path_to_mathlib.txt` lists all the mathlib files.

The goal of this program is to read the file `path_to_mathlib.txt`

and for each file, ask o3-mini to generate list of JSON objects of the form:
{ "prompt": <INFORMAL_LEAN>, "completion": <LEAN_CODE> }

Where:
* <INFORMAL_LEAN> is the human readable description of the Lean code
* <LEAN_CODE> is Lean code corresponding to the description


The program should store the pairs prompt-completion in a json file `mathlib_to_finetuning.json`
containing the list of JSON objects.

Instructions to generate code:
From the specification in the docstring, generate an implementation of the program that satisfies the specification. Keep the docstring with the specification at the top of the file.

"""

import json
import os
from openai import OpenAI
from typing import Dict, List
import logging


PROMPT = """
Your goal is to analyze a Lean4 file, and extract for every Lean snippet, a corresponding
JSON object of the form: { "prompt": <INFORMAL_LEAN>, "completion": <LEAN_CODE> }

where <INFORMAL_LEAN> is the human readable description of the Lean snippet, and <LEAN_CODE> is the Lean snippet associated with the description.

Provide the JSON objects for the following Lean snippet:
[ { "prompt": <DESCRIPTION1>, "completion": <COMPLETION1> },
  { "prompt": <DESCRIPTION1>, "completion": <COMPLETION2> },
  ...
]

"""


def ask_o3_mini(client, file_content):
    # Merged function: builds the API messages, sends the request, and parses the JSON response.
    messages = [
        {"role": "system", "content": "You are a helpful assistant. " + PROMPT},
        {
            "role": "user",
            "content": "*** BEGINNING LEAN FILE: *** \n"
            + file_content
            + "\n *** END OF LEAN FILE ***",
        },
    ]
    try:
        response = client.chat.completions.create(model="o3-mini", messages=messages)
        response_text = response.choices[0].message.content.strip()
        print(response_text)
        return json.loads(response_text)
    except Exception as e:
        logging.error(f"Error calling o3-mini API: {e}")
        return []


def main():
    client = OpenAI(api_key=os.environ.get("OPENAI_API_KEY"))

    # Read mathlib file paths from 'path_to_mathlib.txt'
    with open("path_to_mathlib.txt", "r") as f:
        mathlib_paths = [line.strip() for line in f if line.strip()]

    results = []
    for path in mathlib_paths:
        print(f"Processing {path}")
        if not os.path.exists(path):
            print(f"Warning: {path} does not exist.")
            continue
        with open(path, "r") as file:
            content = file.read()
        json_objects = ask_o3_mini(client, content)
        results.extend(json_objects)
        print(json.dumps(json_objects, indent=2))

    # Write the prompt-completion pairs to JSON file
    with open("mathlib_to_finetuning.json", "w") as out_file:
        json.dump(results, out_file, indent=2)


if __name__ == "__main__":
    main()
