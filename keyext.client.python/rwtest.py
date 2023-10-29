import enum
import abc
import typing
from abc import abstractmethod


class ExampleDesc:
    """"""

    name: str
    description: str


class ProofScriptCommandDesc:
    """"""


class ProofMacroDesc:
    """"""

    name: str
    category: str
    description: str
    scriptCommandName: str


class TraceValue(enum.Enum):
    """"""

    Off = None
    Message = None
    All = None


class SetTraceParams:
    """"""

    value: TraceValue


class EnvironmentId:
    """"""

    envId: str


class ProofId:
    """"""

    env: EnvironmentId
    proofId: str


class TreeNodeDesc:
    """"""


class TreeNodeId:
    """"""

    id: str


class NodeId:
    """"""

    proofId: ProofId
    nodeId: int


class PrintOptions:
    """"""

    unicode: bool
    width: int
    indentation: int
    pure: bool
    termLabels: bool


class NodeTextId:
    """"""

    nodeId: NodeId
    nodeTextId: int


class NodeTextDesc:
    """"""

    id: NodeTextId
    result: str


class TermActionId:
    """"""

    nodeId: NodeId
    pio: str
    id: str


class TermActionKind(enum.Enum):
    """"""

    BuiltIn = None
    Script = None
    Macro = None
    Taclet = None


class TermActionDesc:
    """"""

    commandId: TermActionId
    displayName: str
    description: str
    category: str
    kind: TermActionKind


class List:
    """"""


class SortDesc:
    """"""

    string: str
    documentation: str
    extendsSorts: List
    anAbstract: bool
    s: str


class FunctionDesc:
    """"""

    name: str
    sort: str
    retSort: SortDesc
    argSorts: List
    rigid: bool
    unique: bool
    skolemConstant: bool


class ContractId:
    """"""

    envId: EnvironmentId
    contractId: int


class ContractDesc:
    """"""

    contractId: ContractId
    name: str
    displayName: str
    typeName: str
    htmlText: str
    plainText: str


class LoadParams:
    """"""

    keyFile: str
    javaFile: str
    classPath: List
    bootClassPath: str
    includes: List


class ProblemDefinition:
    """"""

    sorts: List
    functions: List
    predicates: List
    antecTerms: List
    succTerms: List


class LogTraceParams:
    """"""

    messag: str
    verbose: str


class MessageType(enum.Enum):
    """"""

    Unused = None
    Error = None
    Warning = None
    Info = None
    Log = None
    Debug = None


class ShowMessageParams:
    """"""

    type: MessageType
    message: str



class ShowMessageRequestParams:
    """"""

    type: MessageType
    message: str
    actions: typing.List[MessageActionItem]


class MessageActionItem:
    """"""

    title: str


class Range:
    """"""

    start: int
    end: int


class ShowDocumentParams:
    """"""

    uri: str
    external: bool
    takeFocus: bool
    selection: Range


class ShowDocumentResult:
    """"""

    success: bool


class TaskFinishedInfo:
    """"""


class TaskStartedInfo:
    """"""


class KeyServer():
    def env_contracts(self, arg0: EnvironmentId) -> typing.List[ContractDesc]:
        """"""

        return self.rpc.call_sync("env/contracts", )

    def env_functions(self, arg0: EnvironmentId) -> typing.List[FunctionDesc]:
        """"""

        return self.rpc.call_sync("env/functions", )

    def env_openContract(self, arg0: ContractId) -> ProofId:
        """"""

        return self.rpc.call_sync("env/openContract", )

    def env_sorts(self, arg0: EnvironmentId) -> typing.List[SortDesc]:
        """"""

        return self.rpc.call_sync("env/sorts", )

    def examples_list(self, ) -> typing.List[ExampleDesc]:
        """"""

        return self.rpc.call_sync("examples/list", )

    def goal_actions(self, arg0: NodeTextId, arg1: int) -> typing.List[TermActionDesc]:
        """"""

        return self.rpc.call_sync("goal/actions", )

    def goal_apply_action(self, arg0: TermActionId) -> typing.List[TermActionDesc]:
        """"""

        return self.rpc.call_sync("goal/apply_action", )

    def goal_free(self, arg0: NodeTextId):
        """"""

        return self.rpc.call_async("goal/free", )

    def goal_print(self, arg0: NodeId, arg1: PrintOptions) -> NodeTextDesc:
        """"""

        return self.rpc.call_sync("goal/print", )

    def loading_load(self, arg0: LoadParams) -> typing.Union[EnvironmentId, ProofId]:
        """"""

        return self.rpc.call_sync("loading/load", )

    def loading_loadExample(self, arg0: str) -> ProofId:
        """"""

        return self.rpc.call_sync("loading/loadExample", )

    def loading_loadKey(self, arg0: str) -> ProofId:
        """"""

        return self.rpc.call_sync("loading/loadKey", )

    def loading_loadProblem(self, arg0: ProblemDefinition) -> ProofId:
        """"""

        return self.rpc.call_sync("loading/loadProblem", )

    def loading_loadTerm(self, arg0: str) -> ProofId:
        """"""

        return self.rpc.call_sync("loading/loadTerm", )

    def meta_available_macros(self, ) -> typing.List[ProofMacroDesc]:
        """"""

        return self.rpc.call_sync("meta/available_macros", )

    def meta_available_script_commands(self, ) -> typing.List[ProofScriptCommandDesc]:
        """"""

        return self.rpc.call_sync("meta/available_script_commands", )

    def meta_version(self, ) -> str:
        """"""

        return self.rpc.call_sync("meta/version", )

    def proofTree_children(self, arg0: ProofId, arg1: TreeNodeId) -> typing.List[TreeNodeDesc]:
        """"""

        return self.rpc.call_sync("proofTree/children", )

    def proofTree_root(self, arg0: ProofId) -> TreeNodeDesc:
        """"""

        return self.rpc.call_sync("proofTree/root", )

    def proofTree_subtree(self, arg0: ProofId, arg1: TreeNodeId) -> typing.List[TreeNodeDesc]:
        """"""

        return self.rpc.call_sync("proofTree/subtree", )

    def server_exit(self, ):
        """"""

        return self.rpc.call_async("server/exit", )

    def server_setTrace(self, arg0: SetTraceParams):
        """"""

        return self.rpc.call_async("server/setTrace", )

    def server_shutdown(self, ) -> bool:
        """"""

        return self.rpc.call_sync("server/shutdown", )


class Client(abc.ABCMeta):
    @abstractmethod
    def client_logTrace(self, arg0: LogTraceParams):
        """"""

        pass

    @abstractmethod
    def client_sayHello(self, arg0: str):
        """"""

        pass

    @abstractmethod
    def client_showDocument(self, arg0: ShowDocumentParams) -> ShowDocumentResult:
        """"""

        pass

    @abstractmethod
    def client_sm(self, arg0: ShowMessageParams):
        """"""

        pass

    @abstractmethod
    def client_userResponse(self, arg0: ShowMessageRequestParams) -> MessageActionItem:
        """"""

        pass
