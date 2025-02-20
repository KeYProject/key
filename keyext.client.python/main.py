import socket
from keyapi import LspEndpoint, LoadParams, StreategyOptions
from keyapi.server import NetKeY
from keyapi.rpc import JsonRpcEndpoint

def configure_callbacks(key):
    key.register_notification("client/taskStarted", lambda param: print("[KeY Notification] Task started"))
    key.register_notification("client/taskFinished", lambda param: print("[KeY Notification] Task finished"))
    key.register_notification("client/taskProgress", lambda param: print("[KeY Notification] Task progress: ", param))

if __name__ == "__main__":
    target = ("localhost", 5151)

    with NetKeY(target) as key:
        print(key.meta_version())
        configure_callbacks(key)
        envHandle = key.loading_load(
            LoadParams("/home/samuel/Dokumente/Projects/KeY/key/key.core.example/example/IntegerUtil.java",
                       None,
                       None,
                       None))

        contracts = key.env_contracts(envHandle)

        print([c.contractId for c in contracts])

        proof_id = key.env_openContract(contracts[1].contractId)

        print(proof_id.proofId)

        print("Loading Root Node:")
        root_node = key.proofTree_root(proof_id)

        print("Root Node: ",root_node.name)

        proof_status = key.proof_auto(proof_id, StreategyOptions())
        print("Open goals: ", proof_status.openGoals)
        #print("Closed goals: ", proof_status.closedGoals)

    print("Terminating")
