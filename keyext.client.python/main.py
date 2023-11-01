import socket
from keyapi import LspEndpoint, LoadParams
from keyapi.server import KeyServer
from keyapi.rpc import JsonRpcEndpoint

if __name__ == "__main__":
    target = ("localhost", 5151)

    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.connect(target)
        input = s.makefile("r", newline="\r\n")
        output = s.makefile("w", newline="\r\n")

        rpc_endpoint = JsonRpcEndpoint(input, output)
        endpoint = LspEndpoint(rpc_endpoint)
        endpoint.start()

        key = KeyServer(endpoint)
        print(key.meta_version())
        ex = key.examples_list()
        print(ex)

        proofHandle = key.loading_load(
            LoadParams("/home/weigl/work/key/key.ui/examples/standard_key/prop_log/contraposition.key",
                       None, None, None, None))

        print(proofHandle)
