from __future__ import annotations
from .keydata import *
from .rpc import ServerBase

import enum
import abc
import typing
from abc import abstractmethod
class KeyServer(ServerBase):

    def __init__(self, endpoint : LspEndpoint):
        super().__init__(endpoint)

    def env_contracts(self, env : EnvironmentId) -> typing.List[ContractDesc]:
       """"""

       return self._call_sync("env/contracts", [env])

    def env_functions(self, env : EnvironmentId) -> typing.List[FunctionDesc]:
       """"""

       return self._call_sync("env/functions", [env])

    def env_openContract(self, contractId : ContractId) -> ProofId:
       """"""

       return self._call_sync("env/openContract", [contractId])

    def env_sorts(self, env : EnvironmentId) -> typing.List[SortDesc]:
       """"""

       return self._call_sync("env/sorts", [env])

    def examples_list(self, ) -> typing.List[ExampleDesc]:
       """"""

       return self._call_sync("examples/list", [])

    def goal_actions(self, id : NodeTextId, pos : int) -> typing.List[TermActionDesc]:
       """"""

       return self._call_sync("goal/actions", [id , pos])

    def goal_apply_action(self, id : TermActionId) -> typing.List[TermActionDesc]:
       """"""

       return self._call_sync("goal/apply_action", [id])

    def goal_free(self, id : NodeTextId):
        """"""

        return self._call_async("goal/free", [id])

    def goal_print(self, id : NodeId, options : PrintOptions) -> NodeTextDesc:
       """"""

       return self._call_sync("goal/print", [id , options])

    def loading_load(self, params : LoadParams) -> typing.Union[EnvironmentId, ProofId]:
       """"""

       return self._call_sync("loading/load", [params])

    def loading_loadExample(self, id : str) -> ProofId:
       """"""

       return self._call_sync("loading/loadExample", [id])

    def loading_loadKey(self, content : str) -> ProofId:
       """"""

       return self._call_sync("loading/loadKey", [content])

    def loading_loadProblem(self, problem : ProblemDefinition) -> ProofId:
       """"""

       return self._call_sync("loading/loadProblem", [problem])

    def loading_loadTerm(self, term : str) -> ProofId:
       """"""

       return self._call_sync("loading/loadTerm", [term])

    def meta_available_macros(self, ) -> typing.List[ProofMacroDesc]:
       """"""

       return self._call_sync("meta/available_macros", [])

    def meta_available_script_commands(self, ) -> typing.List[ProofScriptCommandDesc]:
       """"""

       return self._call_sync("meta/available_script_commands", [])

    def meta_version(self, ) -> str:
       """"""

       return self._call_sync("meta/version", [])

    def proofTree_children(self, proof : ProofId, nodeId : TreeNodeId) -> typing.List[TreeNodeDesc]:
       """"""

       return self._call_sync("proofTree/children", [proof , nodeId])

    def proofTree_root(self, id : ProofId) -> TreeNodeDesc:
       """"""

       return self._call_sync("proofTree/root", [id])

    def proofTree_subtree(self, proof : ProofId, nodeId : TreeNodeId) -> typing.List[TreeNodeDesc]:
       """"""

       return self._call_sync("proofTree/subtree", [proof , nodeId])

    def server_exit(self, ):
        """"""

        return self._call_async("server/exit", [])

    def server_setTrace(self, params : SetTraceParams):
        """"""

        return self._call_async("server/setTrace", [params])

    def server_shutdown(self, ) -> bool:
       """"""

       return self._call_sync("server/shutdown", [])

class Client(abc.ABCMeta):
    @abstractmethod
    def client_logTrace(self, params : LogTraceParams):
        """"""

        pass

    @abstractmethod
    def client_sayHello(self, e : str):
        """"""

        pass

    @abstractmethod
    def client_showDocument(self, params : ShowDocumentParams) -> ShowDocumentResult:
        """"""

        pass

    @abstractmethod
    def client_sm(self, params : ShowMessageParams):
        """"""

        pass

    @abstractmethod
    def client_userResponse(self, params : ShowMessageRequestParams) -> MessageActionItem:
        """"""

        pass
