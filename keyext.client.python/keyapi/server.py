import socket
from keyapi import LspEndpoint, LoadParams
from keyapi.server_internal import KeyServer
from keyapi.rpc import JsonRpcEndpoint

class NetKeY(object):
    def __init__(self, target):
        self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.socket.connect(target)
        self.inStream = self.socket.makefile("r", newline="\r\n")
        self.outStream = self.socket.makefile("w", newline="\r\n")

        self.rpc_endpoint = JsonRpcEndpoint(self.inStream, self.outStream)
        self.endpoint = LspEndpoint(self.rpc_endpoint)
        self.endpoint.start()

        self.key = KeyServer(self.endpoint)

    def __enter__(self):
        return self

    def __getattr__(self, item):
        return getattr(self.key, item)

    def register_notification(self, method, callback):
        self.endpoint.notify_callbacks[method] = callback

    def __exit__(self, type, value, traceback):
        self.key.server_exit()
        self.inStream.close()
        self.outStream.close()
        self.socket.close()