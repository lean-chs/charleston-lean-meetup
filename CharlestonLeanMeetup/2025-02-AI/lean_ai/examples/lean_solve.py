"""

** SPECIFICATION **

The file `aime_easy.csv` contains problems and solutions from the AIME contest.

The columns in the csv file are:
- problem_id: the id of the problem
- link: where the problem was taken from
- problem: the statement of the problem
- letter: ignore
- answer: the answer to the problem
- competition: the competition the problem was taken from
- year: the year the problem was taken from
- part: ignore
- number: ignore


The goal of this program is to:
* open the csv file

* read the problems and solutions

* Create `aime_easy_lean_ai.csv` with the following columns:
    - problem_id: the id of the problem
    - answer: the answer to the problem
    - result: the result running Lean solution attempt

* For every problem solve it using the main function from `lean_ai/src/lean_ai/main.py`
    passing the problem and the name of the Lean file for the solution as
  ```
  python3 -m lean_ai.main --question <PROBLEM> --file <PROBLEM_NUMER.lean>
  ```

* Try to run the solution <PROBLEM_NUMBER.lean> using `lean --run <PROBLEM_NUMBER.lean>` and store the result in the aime_easy_lean_ai.csv file


Instructions to generate code:
From the specification in the docstring, generate an implementation of the program that satisfies the specification.

"""

import csv
import subprocess


def run_lean_ai(problem, lean_filename):
    # Run the lean_ai main function
    cmd = [
        "python3",
        "-m",
        "lean_ai.main",
        "--question",
        problem,
        "--file",
        lean_filename,
    ]
    try:
        subprocess.run(cmd, check=True)
    except subprocess.CalledProcessError as e:
        print(f"Error running lean_ai for {lean_filename}: {e}")


def run_lean_file(lean_filename):
    # Run the lean file and capture output
    cmd = ["lean", "--run", lean_filename]
    try:
        result = subprocess.run(
            cmd, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
        )
        return result.stdout.strip()
    except subprocess.CalledProcessError as e:
        return f"Error: {e.stderr.strip()}"


PROMPT = """
Write a Lean program that implements the problem. The program should have a main function that when it runs computes the solution to the problem and prints it to the console.

"""


def main():
    input_csv = "examples/aime_easy.csv"
    output_csv = "examples/aime_easy_lean_ai.csv"

    with open(input_csv, newline="", encoding="utf-8") as fin, open(
        output_csv, "w", newline="", encoding="utf-8"
    ) as fout:
        reader = csv.DictReader(fin)
        writer = csv.DictWriter(fout, fieldnames=["problem_id", "answer", "result"])
        writer.writeheader()

        cnt = 0

        for row in reader:
            problem_id = row["problem_id"]
            problem = row["problem"]
            answer = row["answer"]
            lean_filename = f"examples/generated_lean/{problem_id}.lean"

            # Solve the problem using lean_ai main function
            run_lean_ai(PROMPT + problem, lean_filename)

            # Run the Lean solution and capture result
            result = run_lean_file(lean_filename)

            print(f"Problem {problem_id}: {problem}")
            print(f"Lean file: {lean_filename}")
            print(f"Result: {result}")
            print(f"Answer: {answer}")

            # truncate the result its last line and strip it from whitespaces
            result = result[-1].strip()

            writer.writerow(
                {"problem_id": problem_id, "answer": answer, "result": result}
            )

            if cnt > 10:
                break
            # abort prematurely
            # break


if __name__ == "__main__":
    main()
