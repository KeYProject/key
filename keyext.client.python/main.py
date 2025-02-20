import socket
from keyapi import LspEndpoint, LoadParams, StreategyOptions
from keyapi.server import NetKeY, KeYEnv, KeYProof
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

        params = LoadParams("/home/samuel/Dokumente/Projects/KeY/key/key.core.example/example/IntegerUtil.java",
       None,
       None,
       None)

        with KeYEnv(key, params) as env:
            contracts = env.contracts()

            print("Found the following contracts: ")
            print("\n".join([("- "+str(c.contractId)) for c in contracts]))

            i = 0
            with KeYProof(key, contracts[i]) as proof:
                print("Proof for contract: ", contracts[i].contractId)

                root = proof.root()
                print("Root Node: ", root.name)

                status = proof.auto(StreategyOptions())
                print("Open goals: ", status.openGoals)

    print("Terminating")
