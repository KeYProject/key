import abc
import json
from abc import abstractmethod
from multiprocessing import Process, SimpleQueue, Lock, Value


class Client(abc.ABC):
    @abstractmethod
    def handle(self, response):
        pass


class JsonRPCHandler:
    client: Client

    def __init__(self, in_stream, out_stream):
        self.input = in_stream
        self.out = out_stream
        self.__id = 0
        self.client: Client

        self._events = dict()
        self._responses = dict()

        # t: Process = Process(target=self.__read)
        # t.start()

    def read_message(self):
        length = 0
        for clength in self.input.readlines():
            if clength.startswith("Content-Length:"):
                length = int(clength[14:])
                break

        payload = self.input.read(2 + length)
        r = json.loads(payload)
        if "id" in r:  # JSON response for request
            rid = r["id"]
            # self._responses[rid] = r
            # if rid in self._events:
            #    self._events[rid].set()
        else:  # JSON notification
            self.client.handle(r)
        return r

    def __read(self):
        while True:
            self.read_message()

    # def __create_event(self, number):
    #    self._events[number] = Event()

    def _send(self, method, params):
        self.__id += 1
        id = self.__id
        # self.__create_event(self.__id)
        req = {"jsonrpc": "2.0", "method": method, "params": params, "id": self.__id}

        self._write(json.dumps(req))
        # self._wait_for(self.__id)

        r = dict()
        while "id" in r and str(r[id]) != str(id):
            r = self.read_message()
        return r

    def _write(self, msg):
        length = len(msg)
        self.out.write(f"Content-Length: {length}\r\n")
        self.out.write("\r\n")
        self.out.write(msg)
        self.out.write("\r\n")
        self.out.flush()

   # def _wait_for(self, rid):
   #     self._events[rid].wait()
