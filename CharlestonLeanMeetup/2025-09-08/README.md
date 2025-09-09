# Model deployment

On vast.ai using the vLLM image

Following the instructions at
https://cloud.vast.ai/template/readme/76694f014474320e7adfca3673cd30c5


Using some L4/L40 instances at $0.5/hour

```bash
# Connect to the machine
ssh -i ~/.ssh/vastai -p 6451 root@IP_ADDRESS -L 8080:localhost:8080
# this works
ssh -i ~/.ssh/vastai -p 6451 root@IP_ADDRESS -L 8000:0.0.0.0:8000


# the vast vLLM image starts vllm by default, so we need to stop it so we can deploy
# the model we want
supervisorctl stop vllm

# serving
vllm serve "Goedel-LM/Goedel-Prover-V2-8B" --max-model-len 17000


# test the endpoint on the host machine deploying the model
curl -X POST "http://0.0.0.0:8000/v1/chat/completions" \
    -H "Content-Type: application/json" \
    --data '{
            "model": "Goedel-LM/Goedel-Prover-V2-8B",
            "messages": [
                    {
                            "role": "user",
                            "content": "Prove 2+2 =5"
                    }
            ]
    }'



# test the endpoint on the local machine remotely
curl -X POST "http://localhost:8000/v1/chat/completions" \
    -H "Content-Type: application/json" \
    --data '{
            "model": "Goedel-LM/Goedel-Prover-V2-8B",
            "messages": [
                    {
                            "role": "user",
                            "content": "Prove 2+2 =5"
                    }
            ]
    }'

```


# Create MCP server with Godel-Prover-V2


## installation
https://modelcontextprotocol.io/docs/develop/build-server

```bash
curl -LsSf https://astral.sh/uv/install.sh | sh

#Create a new directory for our project
uv init mcp_server
cd mcp_server

# Create virtual environment and activate it
uv venv
source .venv/bin/activate

# Install dependencies
uv add "mcp[cli]" httpx
uv pip install httpx mcp


python mcp_server.py
```

# Codex uses MCP server

In `~/.codex/config.toml`

```bash
[mcp_servers.local-llm]
command = "python"
args = ["PATH_TO/mcp_server/mcp_server.py"]
env = { LLM_BASE_URL = "http://localhost:8000", LLM_MODEL = "Goedel-LM/Goedel-Prover-V2-8B" }
```