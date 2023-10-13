import socket
from keyapi import KeyStub, KeyClient

if __name__ == "__main__":
    target = ("localhost", 5151)

    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.connect(target)
        input = s.makefile("r", newline="\r\n")
        output = s.makefile("w", newline="\r\n")
        stub = KeyStub(input, output)
        stub.client = KeyClient()
        print(stub.list_examples())
