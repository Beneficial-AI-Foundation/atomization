import asyncio
import json
import logging
from typing import Any, Callable


class JsonRpcTransport:
    def __init__(self, cmd: list[str]):
        self.logger = logging.getLogger(f"{__name__}.{self.__class__.__name__}")
        self.cmd = cmd
        self.proc: asyncio.subprocess.Process | None = None
        self._id = 0
        self._resp_handlers: dict[int, asyncio.Future[Any]] = {}
        self._notification_handlers: dict[str, list[Callable[[Any], None]]] = {}
        self._read_task: asyncio.Task | None = None

    async def start(self):
        """Start the LSP server process and begin reading responses."""
        self.proc = await asyncio.create_subprocess_exec(
            *self.cmd,
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        self._read_task = asyncio.create_task(self._read_loop())

    async def _read_loop(self):
        if not self.proc or not self.proc.stdout:
            return

        while True:
            try:
                header_bytes = await self.proc.stdout.readline()
                if not header_bytes:
                    break

                header = header_bytes.decode("utf-8").strip()
                if header.startswith("Content-Length:"):
                    length = int(header.split(":")[1].strip())
                    # skip blank line
                    await self.proc.stdout.readline()
                    body_bytes = await self.proc.stdout.read(length)
                    body = body_bytes.decode("utf-8")
                    msg = json.loads(body)
                    self.logger.debug(f"Received: {msg}")

                    if "id" in msg:
                        # Response to a request
                        if "error" in msg:
                            self.logger.error(f"LSP Error: {msg['error']}")
                            if future := self._resp_handlers.pop(msg["id"], None):
                                future.set_exception(
                                    Exception(f"LSP Error: {msg['error']}")
                                )
                        else:
                            if future := self._resp_handlers.pop(msg["id"], None):
                                future.set_result(msg.get("result"))
                    elif "method" in msg:
                        # Notification from server
                        method = msg["method"]
                        if method in self._notification_handlers:
                            for handler in self._notification_handlers[method]:
                                handler(msg.get("params"))
            except Exception as e:
                self.logger.error(f"Error in read loop: {e}")
                break

    async def send(self, method: str, params: dict) -> Any:
        """Send a request and wait for the response."""
        if not self.proc or not self.proc.stdin:
            raise RuntimeError("Transport not started")

        self._id += 1
        req = {"jsonrpc": "2.0", "id": self._id, "method": method, "params": params}
        data = json.dumps(req)
        hdr = f"Content-Length: {len(data)}\r\n\r\n"
        message = hdr + data
        self.logger.debug(f"Sending request: {req}")

        # Create future for response
        future = asyncio.Future()
        self._resp_handlers[self._id] = future

        # Send the request
        self.proc.stdin.write(message.encode("utf-8"))
        await self.proc.stdin.drain()

        # Wait for response
        return await future

    async def notify(self, method: str, params: dict) -> None:
        """Send a notification (no response expected)."""
        if not self.proc or not self.proc.stdin:
            raise RuntimeError("Transport not started")

        req = {"jsonrpc": "2.0", "method": method, "params": params}
        data = json.dumps(req)
        hdr = f"Content-Length: {len(data)}\r\n\r\n"
        message = hdr + data
        self.logger.debug(f"Sending notification: {req}")
        self.proc.stdin.write(message.encode("utf-8"))
        await self.proc.stdin.drain()

    def add_notification_handler(
        self, method: str, handler: Callable[[Any], None]
    ) -> None:
        """Add handler for server notifications."""
        if method not in self._notification_handlers:
            self._notification_handlers[method] = []
        self._notification_handlers[method].append(handler)

    async def close(self):
        """Close the transport and cleanup resources."""
        if self._read_task:
            self._read_task.cancel()
            try:
                await self._read_task
            except asyncio.CancelledError:
                pass

        if self.proc:
            self.proc.terminate()
            await self.proc.wait()
