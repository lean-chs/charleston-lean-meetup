# server.py
import os
import httpx
from mcp.server.fastmcp import FastMCP

# Configure via env vars if you like
LLM_BASE_URL = os.getenv("LLM_BASE_URL", "http://localhost:8000")
LLM_API_KEY = os.getenv("LLM_API_KEY", "")
LLM_MODEL = os.getenv("LLM_MODEL", "Goedel-LM/Goedel-Prover-V2-8B")

mcp = FastMCP("local-llm")


@mcp.tool()
async def generate(prompt: str, system: str | None = None) -> str:
    """Generate a completion with the local LLM."""
    # OpenAI-compatible chat payload; tweak if your server differs
    payload = {
        "model": LLM_MODEL,
        "messages": (
            ([{"role": "system", "content": system}] if system else [])
            + [{"role": "user", "content": prompt}]
        ),
    }
    headers = {"Authorization": f"Bearer {LLM_API_KEY}"} if LLM_API_KEY else {}
    async with httpx.AsyncClient(timeout=90) as client:
        r = await client.post(
            f"{LLM_BASE_URL}/v1/chat/completions", json=payload, headers=headers
        )
        r.raise_for_status()
        data = r.json()
        return data["choices"][0]["message"]["content"]


if __name__ == "__main__":
    # Use stdio transport so Codex can spawn/pipe to it
    mcp.run(transport="stdio")
