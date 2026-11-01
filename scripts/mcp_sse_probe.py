#!/usr/bin/env python3
"""Standalone probe for the KeY MCP server (MCP over HTTP + Server-Sent Events).

Connects to the SSE endpoint like a real MCP client, using only the Python
standard library (no dependencies): it reads the ``endpoint`` event, performs
the MCP ``initialize`` handshake, lists the tools and — optionally — calls one
of them. Every JSON-RPC exchange is printed.

Usage:
    python3 scripts/mcp_sse_probe.py [SSE_URL] [--token TOKEN] [--call TOOL]
                                    [--args JSON] [--timeout SECONDS]

Examples:
    python3 scripts/mcp_sse_probe.py http://127.0.0.1:6001/sse
    python3 scripts/mcp_sse_probe.py http://127.0.0.1:6001/sse --token s3cret \\
        --call read_file --args '{"path": "/tmp/x.txt"}'

Exits with 0 if the server answered the handshake and the tool list, 1 on any
protocol error.
"""

import argparse
import json
import queue
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request

# ---------------------------------------------------------------- SSE reading

class SseStream:
    """Reads an ``text/event-stream`` response and dispatches its events."""

    def __init__(self, url: str, token: str, timeout: float):
        self.url = url
        self.timeout = timeout
        headers = {
            "Accept": "text/event-stream",
            "Cache-Control": "no-cache",
        }
        if token:
            headers["Authorization"] = "Bearer " + token
        try:
            self.response = urllib.request.urlopen(
                urllib.request.Request(url, headers=headers), timeout=timeout)
        except urllib.error.HTTPError as e:
            hint = " (wrong or missing bearer token?)" if e.code == 401 else ""
            raise RuntimeError(f"SSE connect -> HTTP {e.code}{hint}") from None
        ctype = self.response.headers.get("Content-Type", "")
        if "text/event-stream" not in ctype:
            raise RuntimeError(
                f"unexpected Content-Type '{ctype}', expected text/event-stream "
                f"(HTTP {self.response.status}). Is the URL an SSE endpoint?")
        self.endpoint: str | None = None  # message endpoint, sent by the server
        self.events: queue.Queue[dict] = queue.Queue()

    def read_forever(self) -> None:
        """Parses the stream in the background, filling ``events``."""
        event, data_lines = "message", []
        try:
            for raw in self.response:
                line = raw.decode("utf-8").rstrip("\r\n")
                if not line:  # blank line = end of event
                    if data_lines:
                        self.events.put({"event": event,
                                         "data": "\n".join(data_lines)})
                    event, data_lines = "message", []
                elif line.startswith(":"):
                    pass  # comment / keep-alive
                elif ":" in line:
                    field, _, value = line.partition(":")
                    value = value.removeprefix(" ")
                    if field == "event":
                        event = value
                    elif field == "data":
                        data_lines.append(value)
                    # 'id', 'retry' etc. are irrelevant here
        except Exception:  # connection closed or timed out
            pass
        finally:
            self.events.put({"event": "__closed__", "data": ""})

    def next_event(self, wanted: list[str]) -> tuple[str, dict]:
        """Returns the first event whose name is in ``wanted``; fails on close."""
        deadline = time.monotonic() + self.timeout
        while time.monotonic() < deadline:
            try:
                ev = self.events.get(timeout=max(0.1, deadline - time.monotonic()))
            except queue.Empty:
                break
            if ev["event"] == "__closed__":
                raise RuntimeError("the SSE stream closed unexpectedly")
            if ev["event"] in wanted:
                return ev["event"], ev
        raise RuntimeError(f"no {wanted} event within {self.timeout}s")

    def close(self) -> None:
        self.response.close()


# ---------------------------------------------------------------- JSON-RPC

class Probe:
    def __init__(self, url: str, token: str, timeout: float):
        self.token = token
        self.timeout = timeout
        self.stream = SseStream(url, token, timeout)
        parsed = urllib.parse.urlparse(url)
        self.base = f"{parsed.scheme}://{parsed.netloc}"
        self.next_id = 0

    def run(self, tool_to_call: str | None, call_args: dict) -> int:
        threading.Thread(target=self.stream.read_forever, daemon=True).start()

        # 1. the server announces the message endpoint on the stream
        event, ev = self.stream.next_event(["endpoint"])
        endpoint = urllib.parse.urljoin(self.base + urllib.parse.urlparse(self.stream.url).path,
                                        ev["data"])
        print(f"[endpoint] {ev['data']}  ->  {endpoint}")

        # 2. initialize handshake
        info = self.server_info = self.request(endpoint, {
            "method": "initialize",
            "params": {
                "protocolVersion": "2024-11-05",
                "capabilities": {},
                "clientInfo": {"name": "mcp-sse-probe", "version": "1.0"},
            },
        })
        sinfo = info.get("result", {}).get("serverInfo", {})
        print(f"[initialize] server={sinfo.get('name')} v{sinfo.get('version')} "
              f"protocol={info.get('result', {}).get('protocolVersion')}")
        self.notify(endpoint, {"method": "notifications/initialized"})

        # 3. list the tools
        tools = self.request(endpoint, {"method": "tools/list"})
        names = [t["name"] for t in tools.get("result", {}).get("tools", [])]
        print(f"[tools/list] {len(names)} tools: {', '.join(names) or '(none)'}")

        # 4. optionally call a tool
        if tool_to_call:
            result = self.request(endpoint, {
                "method": "tools/call",
                "params": {"name": tool_to_call, "arguments": call_args},
            })
            content = result.get("result", {}).get("content", [])
            for item in content:
                text = item.get("text", json.dumps(item))
                print(f"[tools/call {tool_to_call}] {text[:500]}")
            if result.get("result", {}).get("isError"):
                print(f"warning: tool call reported isError=true", file=sys.stderr)
        self.stream.close()
        return 0

    def request(self, endpoint: str, body: dict) -> dict:
        """Sends a JSON-RPC request and waits for the matching response on the stream."""
        self.next_id += 1
        body = dict(body, jsonrpc="2.0", id=self.next_id)
        self.send(endpoint, body)
        wanted_id = self.next_id
        while True:
            _, ev = self.stream.next_event(["message"])
            message = json.loads(ev["data"])
            if message.get("id") == wanted_id:
                if "error" in message:
                    raise RuntimeError(
                        f"{body['method']} failed: {json.dumps(message['error'])}")
                print(f"[<-] {body['method']} ok")
                return message
            # a different (e.g. server-initiated) message; keep waiting

    def notify(self, endpoint: str, body: dict) -> None:
        body = dict(body, jsonrpc="2.0")
        self.send(endpoint, body)  # notifications expect no response

    def send(self, endpoint: str, body: dict) -> None:
        data = json.dumps(body).encode("utf-8")
        headers = {"Content-Type": "application/json", "Accept": "application/json"}
        if self.token:
            headers["Authorization"] = "Bearer " + self.token
        req = urllib.request.Request(endpoint, data=data, headers=headers, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                if resp.status not in (200, 202):
                    raise RuntimeError(f"POST returned HTTP {resp.status}")
        except urllib.error.HTTPError as e:
            detail = e.read().decode("utf-8", "replace")[:200]
            hint = " (missing bearer token?)" if e.code == 401 else ""
            raise RuntimeError(f"POST {body.get('method')} -> HTTP {e.code}{hint}: {detail}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("url", nargs="?", default="http://127.0.0.1:6001/sse",
                    help="the SSE endpoint, e.g. http://127.0.0.1:6001/sse")
    ap.add_argument("--token", default="", help="bearer token if one is set in the settings")
    ap.add_argument("--call", metavar="TOOL", default=None, help="also call this tool")
    ap.add_argument("--args", metavar="JSON", default="{}",
                    help="arguments for --call (default {})")
    ap.add_argument("--timeout", type=float, default=10.0,
                    help="seconds to wait for each step (default 10)")
    args = ap.parse_args()

    try:
        call_args = json.loads(args.args)
    except json.JSONDecodeError as e:
        print(f"invalid --args: {e}", file=sys.stderr)
        return 1

    probe = None
    try:
        probe = Probe(args.url, args.token, args.timeout)
        return probe.run(args.call, call_args)
    except RuntimeError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("aborted", file=sys.stderr)
        return 1
    finally:
        if probe is not None:
            probe.stream.close()


if __name__ == "__main__":
    sys.exit(main())
