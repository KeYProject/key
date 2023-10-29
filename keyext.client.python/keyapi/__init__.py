from keyapi.rpc import *

class KeyStub(JsonRPCHandler):
    def __init__(self, input, output):
        super().__init__(input, output)

    def list_examples(self):
        return self._send("examples/list", [])
