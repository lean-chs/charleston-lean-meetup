"""
This program is a utility tool that allows a user to ask an AI to write or modify a single Lean code file.

From the users perspective it is a simple command line tool that takes a question as input will let the AI write or modify a Lean code file.

High level description of the internal workings of the program:
- parse the user input to extract the question/problem the user is asking
- open the prompt file providing the instructions to the AI
- The AI will be provided the prompt, the user input, a view of the Lean code file and the output of the compiler.
- The AI then provide a response whether it thinks the code is correct and the problem is solved or some modifications to the Lean code.
- The program will then run the Lean code and provide the output to the AI.
- The previous 2 steps will be repeated until the AI provides a correct solution, and this loop will be repeated for a maximum number of iterations is reached.


Here are the main components of the program:

- (REQ:DEFAULT_LEAN_FILE) DEAFULT_LEAN_FILE: the name of the default Lean file. Set to `spec.lean`.

- (REQ:parse_input) `parse_input` function:
  This function parses the user input to extract the question/problem the user
  is asking and the lean file to modify if provided.
  The cli arguments are parsed using the `argparse` library.
  The arguments are `--question` and `--file`. If `--file` is not provided default to DEFAULT_LEAN_FILE.

- (REQ:Ai) `Ai` class:
  This class is the main class of the program.
  It contains the variables and the main loop of the program calling into helper functions.

- (REQ:load_prompt) `load_prompt` function:
  this function loads the prompt template from a file `prompt.txt` and store it in a instance variable.

- (REQ:create_messages) `create_messages` function:
  this function creates the messages to send to the AI.
  The messages are made of the prompt, the user input in a `PROBLEM` section,
  the view of the Lean code in a `VIEW` section and the output of the compiler
  in a `TOOL_OUTPUT` section.

- (REQ:send_message) `send_message` function:
  This function sends the messages to the AI, waits for a response and returns the text contained in the response.
  It uses the OpenAI API to send the messages to the `o3-mini` model.
  The content of the response contains some text that is extracted and is returned.

- (REQ:parse_ai_response) `parse_ai_response` function:
  This function parses the response from the AI.
  The response of the AI is expected to be structured as follows
    - **notes** followed by,
    - a separation marker `SEPARATE_NOTES_FROM_JSON`, following by
    - a JSON object in text form.
  For example:
  `these are my notes SEPARATE_NOTES_FROM_JSON {"done": true}`
  Once the notes and JSON object are extracted, the JSON object is validated and returned.
  The JSON object can be one the two following options:
    - (REQ:llm_json_done)
      `{ done: true}`
      the AI thinks the problem is solved
    - (REQ:llm_json_graft)
      ```
      { done: false,
         graft: {
           line_start: <LINE_START>,
           line_end:<LINE_END>,
           block: [ LINE_CONTENT_1, ... , LINE_CONTENT_n]
         },
      }
      ```
      the AI provides a block of modifications to the Lean code line-by-line. The pairs in the `modification_block` list are made of a line number and the new content of the line to modify. The sequence of pairs is supposed to be ordered by line number. The modifications are supposed to be applied in order to the Lean code.

- (REQ:main_loop) `main_loop` function:
  this function is the main loop of the program.
    In a loop it will:
    - create the messages to send to the AI
    - send the messages to the AI
    - parse the response from the AI
    - apply the graft modification to the Lean code
    - run the Lean code
    - store its output
    - read the file and store its content
    - send the content of the file and the output of the compiler to of the compiler to the AI
    - repeat the loop until the AI thinks the problem is solved or a maximum number of iterations is reached

- (REQ:graft_block) `graft_block` function:
  This function applies the graft function to a file.
  Following the requirement REQ:llm_json_graft. This function will take the block and insert it into the file between `line_start` (included) and `line_end` (excluded).
  For example suppose the section of the Lean file is
    134: for i in range(10):
    135:    print(i)
    136: print("done"
  suppose the block=[ "  # print i + 1", "  print(i+1)" ]

  if line_start=135 and line_end=136 then the resulting Lean file will be
    134: for i in range(10):
    135:    # print i + 1
    136:    print(i+1)
    137: print("done")
  so it replaces the line 135 with the two new lines

  if line_start=135 and line_end=135 then the resulting Lean file will be
    134: for i in range(10):
    135:    print(i)
    136:    # print i + 1
    137:    print(i+1)
    138: print("done")
  so when line_start is equal to line_end the block is inserted at the line_start position.





# Development

The program below has been implemented partly by hand and partly using `o3-mini`.

One-shot generation prompt:
Generate an implementation of this program in Python, following the description and set of requirements provided above, and tracing back the implementation to the requirements by annotating the code with comments containing the requirements.

Iteration generation prompt:
TODO

"""

import os
import logging
import subprocess
import argparse
import time

from importlib import resources
from typing import Dict, List
from openai import OpenAI
import requests
import json5 as json


# REQ:DEFAULT_LEAN_FILE
DEFAULT_LEAN_FILE = "spec.lean"

# Added new requirement: read_file function (REQ:read_file)
def read_file(filename: str) -> str:
    # REQ:read_file
    try:
        with open(filename, "r") as f:
            lines = f.readlines()
        numbered_lines = [f"{i+1}: {line.rstrip()}" for i, line in enumerate(lines)]
        return "\n".join(numbered_lines)
    except FileNotFoundError:
        return ""

# General Agent Class
class Ai:

    # init function
    def __init__(self):
        # REQ:Ai
        self.client = OpenAI(api_key=os.environ.get("OPENAI_API_KEY"))
        self.system_prompt = ""
        self.max_iterations = 5

    def load_prompt(self):
        """
        Load the prompt template.
        """
        # REQ:load_prompt
        try:
            with open("prompts/intro.txt") as file:
                prompt = file.read()
            self.system_prompt = prompt
            return prompt
        except FileNotFoundError:
            print(f"File 'intro.txt' not found.")
            return ""

    def parse_input(self):
        # REQ:parse_input
        parser = argparse.ArgumentParser(description="Lean AI utility")
        parser.add_argument("--question", required=True, help="The question/problem for the AI")
        parser.add_argument("--file", default=DEFAULT_LEAN_FILE, help="Lean file to modify")
        args = parser.parse_args()
        return args.question, args.file

    def create_messages(self, lean_code: str, compiler_output: str, question: str) -> List[Dict[str, str]]:
        # REQ:create_messages
        messages = [
            {"role": "system", "content": self.system_prompt},
            {"role": "user", "content": f"PROBLEM:\n{question}"},
            {"role": "user", "content": f"VIEW:\n{lean_code}"},
            {"role": "user", "content": f"TOOL_OUTPUT:\n{compiler_output}"},
        ]
        return messages

    def send_message(self, messages: List[Dict[str, str]]) -> str:
        # REQ:send_message
        try:
            response = self.client.ChatCompletion.create(
                model="o3-mini",
                messages=messages
            )
            response_text = response['choices'][0]['message']['content']
            return response_text
        except Exception as e:
            logging.error(f"Error sending message: {e}")
            return ""

    def parse_ai_response(self, response_text: str) -> Dict:
        # REQ:parse_ai_response
        try:
            notes, json_part = response_text.split("SEPARATE_NOTES_FROM_JSON", 1)
            parsed = json.loads(json_part.strip())
            return parsed
        except Exception as e:
            logging.error(f"Failed to parse AI response: {e}")
            return {}

    def graft_block(self, filename: str, line_start: int, line_end: int, block: List[str]):
        # REQ:graft_block
        try:
            with open(filename, "r") as file:
                lines = file.readlines()
            # Adjust for 1-based indexing
            start_idx = line_start - 1
            end_idx = line_end - 1
            new_lines = lines[:start_idx] + [line + "\n" for line in block] + lines[end_idx:]
            with open(filename, "w") as file:
                file.writelines(new_lines)
        except Exception as e:
            logging.error(f"Error grafting block: {e}")

    def run_lean_code(self, filename: str) -> str:
        # Execute Lean code and capture compiler output.
        try:
            result = subprocess.run(["lean", filename], capture_output=True, text=True)
            return result.stdout + result.stderr
        except Exception as e:
            logging.error(f"Error running lean code: {e}")
            return ""

    def main_loop(self):
        # REQ:main_loop
        question, filename = self.parse_input()
        iteration = 0

        while iteration < self.max_iterations:
            iteration += 1
            # Read current lean file using new read_file function
            lean_code = read_file(filename)
            # Run lean code to obtain compiler output
            compiler_output = self.run_lean_code(filename)
            # Create the AI messages
            messages = self.create_messages(lean_code, compiler_output, question)
            # Send message to AI and receive response
            response_text = self.send_message(messages)
            ai_response = self.parse_ai_response(response_text)

            if ai_response.get("done"):
                print("AI indicates problem solved.")
                break
            elif "graft" in ai_response:
                graft = ai_response["graft"]
                line_start = graft.get("line_start")
                line_end = graft.get("line_end")
                block = graft.get("block")
                self.graft_block(filename, line_start, line_end, block)
            else:
                logging.error("Unexpected AI response format.")
                break

            time.sleep(1)  # Optional delay between iterations

        print("Main loop completed.")

# Entry point to main program
if __name__ == "__main__":
    ai = Ai()
    ai.load_prompt()
    ai.main_loop()
