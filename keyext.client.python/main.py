import socket
from keyapi import LspEndpoint, LoadParams
from keyapi.server import NetKeY
from keyapi.rpc import JsonRpcEndpoint

if __name__ == "__main__":
    target = ("localhost", 5151)

    with NetKeY(target) as key:
        print(key.meta_version())
        envHandle = key.loading_load(
            LoadParams("/home/samuel/Dokumente/Projects/KeY/key/key.core.example/example/IntegerUtil.java",
                       None,
                       None,
                       None))

        contracts = key.env_contracts(envHandle)

        print([c.contractId for c in contracts])

        proof_id = key.env_openContract(contracts[0].contractId)

        print(proof_id.proofId)

        print("Loading Root Node:")
        root_node = key.proofTree_root(proof_id)

        print("Root Node: ",root_node.name)

        key.auto

    print("Terminating")
