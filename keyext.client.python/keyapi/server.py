import socket
from keyapi import LspEndpoint, LoadParams, StrategyOptions
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

class KeYEnv(object):
    def __init__(self, key, load_params : LoadParams):
        self.key = key
        self.envHandle = self.key.loading_load(load_params)

    def contracts(self):
        return self.key.env_contracts(self.envHandle)

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.key.env_dispose(self.envHandle)

class KeYProof(object):
    def __init__(self, key, contract):
        self.key = key
        self.proofHandle = self.key.env_openContract(contract.contractId)

    def __enter__(self):
        return self

    def root(self):
        return self.key.proofTree_root(self.proofHandle)

    def auto(self, options = StrategyOptions(None, None, None, None, None, 10000)):
        return self.key.proof_auto(self.proofHandle, options)

    def goals(self, open_only = False, only_enabled = False):
        return self.key.proof_goals(self.proofHandle, open_only, only_enabled)

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.key.proof_dispose(self.proofHandle)