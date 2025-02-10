import os
from openai import OpenAI


def main():
    client = OpenAI(api_key=os.environ.get("OPENAI_API_KEY"))
    messages = [{"role": "user", "content": "Hello there!"}]
    try:
        response = client.chat.completions.create(model="o3-mini", messages=messages)
        response_text = response.choices[0].message.content.strip()
        print(response_text)
    except Exception as e:
        print(f"API error: {e}")


if __name__ == "__main__":
    main()
