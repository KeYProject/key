from keyapi.rpc import JsonRPCHandler, Client


class KeyClient(Client):
    def __int__(self):
        pass

    def handle(self, res):
        print(res)


class KeyStub(JsonRPCHandler):
    def __init__(self, input, output):
        super().__init__(input, output)

    def list_examples(self):
        return self._send("examples/list", [])
