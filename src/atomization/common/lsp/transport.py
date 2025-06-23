import subprocess
import threading
import json
import logging
from typing import Any, Callable


class JsonRpcTransport:
    def __init__(self, cmd: list[str]):
        self.logger = logging.getLogger(f"{__name__}.{self.__class__.__name__}")
        self.proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=0,
        )
        self._id = 0
        self._resp_handlers: dict[int, Callable[[Any], None]] = {}
        self._notification_handlers: dict[str, list[Callable[[Any], None]]] = {}
        threading.Thread(target=self._read_loop, daemon=True).start()

    def _read_loop(self):
        while True:
            try:
                header = self.proc.stdout.readline()
                if not header:
                    break
                if header.startswith("Content-Length:"):
                    length = int(header.split(":")[1].strip())
                    # skip blank line
                    self.proc.stdout.readline()
                    body = self.proc.stdout.read(length)
                    msg = json.loads(body)
                    self.logger.debug(f"Received: {msg}")

                    if "id" in msg:
                        # Response to a request
                        if "error" in msg:
                            self.logger.error(f"LSP Error: {msg['error']}")
                        if h := self._resp_handlers.pop(msg["id"], None):
                            h(msg.get("result"))
                    elif "method" in msg:
                        # Notification from server
                        method = msg["method"]
                        if method in self._notification_handlers:
                            for handler in self._notification_handlers[method]:
                                handler(msg.get("params"))
            except Exception as e:
                self.logger.error(f"Error in read loop: {e}")
                break

    def send(
        self, method: str, params: dict, handler: Callable[[Any], None] = lambda _: None
    ) -> int:
        self._id += 1
        req = {"jsonrpc": "2.0", "id": self._id, "method": method, "params": params}
        data = json.dumps(req)
        hdr = f"Content-Length: {len(data)}\r\n\r\n"
        message = hdr + data
        self.logger.debug(f"Sending request: {req}")
        self.proc.stdin.write(message)
        self.proc.stdin.flush()
        self._resp_handlers[self._id] = handler
        return self._id

    def notify(self, method: str, params: dict) -> None:
        """Send a notification (no response expected)."""
        req = {"jsonrpc": "2.0", "method": method, "params": params}
        data = json.dumps(req)
        hdr = f"Content-Length: {len(data)}\r\n\r\n"
        message = hdr + data
        self.logger.debug(f"Sending notification: {req}")
        self.proc.stdin.write(message)
        self.proc.stdin.flush()

    def add_notification_handler(
        self, method: str, handler: Callable[[Any], None]
    ) -> None:
        """Add handler for server notifications."""
        if method not in self._notification_handlers:
            self._notification_handlers[method] = []
        self._notification_handlers[method].append(handler)
