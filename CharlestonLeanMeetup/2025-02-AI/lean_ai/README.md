# Installation

Create python environment
```bash
python3 -m venv lean_ai_env
source lean_ai_env/bin/activate
```

Install dependencies
```bash
pip install --upgrade pip
python3 -m pip install openai
python3 -m pip install json5
python3 -m pip install requests
```

Run the program:
```bash
OPENAI_API_KEY=<TOKEN> python3 -m lean_ai.main
```