from __future__ import annotations
import enum
import abc
import typing
from abc import abstractmethod, ABCMeta

class ExampleDesc:
    """"""

    name : str
    """"""

    description : str
    """"""

    def __init__(self, name, description):
        self.name = name
        self.description = description

class ProofMacroDesc:
    """"""

    name : str
    """"""

    category : str
    """"""

    description : str
    """"""

    scriptCommandName : str
    """"""

    def __init__(self, name, category, description, scriptCommandName):
        self.name = name
        self.category = category
        self.description = description
        self.scriptCommandName = scriptCommandName

class ProofScriptCommandDesc:
    """"""

    def __init__(self, ):
        pass


class TraceValue(enum.Enum):
    """"""

    Off = None
    Message = None
    All = None

class SetTraceParams:
    """"""

    value : TraceValue
    """"""

    def __init__(self, value):
        self.value = value

class EnvironmentId:
    """"""

    envId : str
    """"""

    def __init__(self, envId):
        self.envId = envId

class ProofId:
    """"""

    env : EnvironmentId
    """"""

    proofId : str
    """"""

    def __init__(self, env, proofId):
        self.env = env
        self.proofId = proofId

class NodeId:
    """"""

    proofId : ProofId
    """"""

    nodeId : int
    """"""

    def __init__(self, proofId, nodeId):
        self.proofId = proofId
        self.nodeId = nodeId

class List:
    """"""

    def __init__(self, ):
        pass


class NodeDesc:
    """"""

    nodeid : NodeId
    """"""

    branchLabel : str
    """"""

    scriptRuleApplication : bool
    """"""

    children : List
    """"""

    def __init__(self, nodeid, branchLabel, scriptRuleApplication, children):
        self.nodeid = nodeid
        self.branchLabel = branchLabel
        self.scriptRuleApplication = scriptRuleApplication
        self.children = children

class StreategyOptions:
    """"""

    def __init__(self, ):
        pass


class MacroStatistic:
    """"""

    proofId : ProofId
    """"""

    macroId : str
    """"""

    appliedRules : int
    """"""

    closedGoals : int
    """"""

    def __init__(self, proofId, macroId, appliedRules, closedGoals):
        self.proofId = proofId
        self.macroId = macroId
        self.appliedRules = appliedRules
        self.closedGoals = closedGoals

class ProofStatus:
    """"""

    id : ProofId
    """"""

    openGoals : int
    """"""

    closedGoals : int
    """"""

    def __init__(self, id, openGoals, closedGoals):
        self.id = id
        self.openGoals = openGoals
        self.closedGoals = closedGoals

class TreeNodeDesc:
    """"""

    id : NodeId
    """"""

    name : str
    """"""

    def __init__(self, id, name):
        self.id = id
        self.name = name

class TreeNodeId:
    """"""

    id : str
    """"""

    def __init__(self, id):
        self.id = id

class PrintOptions:
    """"""

    unicode : bool
    """"""

    width : int
    """"""

    indentation : int
    """"""

    pure : bool
    """"""

    termLabels : bool
    """"""

    def __init__(self, unicode, width, indentation, pure, termLabels):
        self.unicode = unicode
        self.width = width
        self.indentation = indentation
        self.pure = pure
        self.termLabels = termLabels

class NodeTextId:
    """"""

    nodeId : NodeId
    """"""

    nodeTextId : int
    """"""

    def __init__(self, nodeId, nodeTextId):
        self.nodeId = nodeId
        self.nodeTextId = nodeTextId

class NodeTextDesc:
    """"""

    id : NodeTextId
    """"""

    result : str
    """"""

    def __init__(self, id, result):
        self.id = id
        self.result = result

class TermActionId:
    """"""

    nodeId : NodeId
    """"""

    pio : str
    """"""

    id : str
    """"""

    def __init__(self, nodeId, pio, id):
        self.nodeId = nodeId
        self.pio = pio
        self.id = id

class TermActionKind(enum.Enum):
    """"""

    BuiltIn = None
    Script = None
    Macro = None
    Taclet = None

class TermActionDesc:
    """"""

    commandId : TermActionId
    """"""

    displayName : str
    """"""

    description : str
    """"""

    category : str
    """"""

    kind : TermActionKind
    """"""

    def __init__(self, commandId, displayName, description, category, kind):
        self.commandId = commandId
        self.displayName = displayName
        self.description = description
        self.category = category
        self.kind = kind

class SortDesc:
    """"""

    string : str
    """"""

    documentation : str
    """"""

    extendsSorts : List
    """"""

    anAbstract : bool
    """"""

    s : str
    """"""

    def __init__(self, string, documentation, extendsSorts, anAbstract, s):
        self.string = string
        self.documentation = documentation
        self.extendsSorts = extendsSorts
        self.anAbstract = anAbstract
        self.s = s

class FunctionDesc:
    """"""

    name : str
    """"""

    sort : str
    """"""

    retSort : SortDesc
    """"""

    argSorts : List
    """"""

    rigid : bool
    """"""

    unique : bool
    """"""

    skolemConstant : bool
    """"""

    def __init__(self, name, sort, retSort, argSorts, rigid, unique, skolemConstant):
        self.name = name
        self.sort = sort
        self.retSort = retSort
        self.argSorts = argSorts
        self.rigid = rigid
        self.unique = unique
        self.skolemConstant = skolemConstant

class ContractId:
    """"""

    envId : EnvironmentId
    """"""

    contractId : str
    """"""

    def __init__(self, envId, contractId):
        self.envId = envId
        self.contractId = contractId

class ContractDesc:
    """"""

    contractId : ContractId
    """"""

    name : str
    """"""

    displayName : str
    """"""

    typeName : str
    """"""

    htmlText : str
    """"""

    plainText : str
    """"""

    def __init__(self, contractId, name, displayName, typeName, htmlText, plainText):
        self.contractId = contractId
        self.name = name
        self.displayName = displayName
        self.typeName = typeName
        self.htmlText = htmlText
        self.plainText = plainText

class LoadParams:
    """"""

    problemFile : str
    """"""

    classPath : List
    """"""

    bootClassPath : str
    """"""

    includes : List
    """"""

    def __init__(self, problemFile, classPath, bootClassPath, includes):
        self.problemFile = problemFile
        self.classPath = classPath
        self.bootClassPath = bootClassPath
        self.includes = includes

class ProblemDefinition:
    """"""

    sorts : List
    """"""

    functions : List
    """"""

    predicates : List
    """"""

    antecTerms : List
    """"""

    succTerms : List
    """"""

    def __init__(self, sorts, functions, predicates, antecTerms, succTerms):
        self.sorts = sorts
        self.functions = functions
        self.predicates = predicates
        self.antecTerms = antecTerms
        self.succTerms = succTerms

class LogTraceParams:
    """"""

    messag : str
    """"""

    verbose : str
    """"""

    def __init__(self, messag, verbose):
        self.messag = messag
        self.verbose = verbose

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

    type : MessageType
    """"""

    message : str
    """"""

    def __init__(self, type, message):
        self.type = type
        self.message = message

class ShowMessageRequestParams:
    """"""

    type : MessageType
    """"""

    message : str
    """"""

    actions : List
    """"""

    def __init__(self, type, message, actions):
        self.type = type
        self.message = message
        self.actions = actions

class MessageActionItem:
    """"""

    title : str
    """"""

    def __init__(self, title):
        self.title = title

class Range:
    """"""

    start : int
    """"""

    end : int
    """"""

    def __init__(self, start, end):
        self.start = start
        self.end = end

class ShowDocumentParams:
    """"""

    uri : str
    """"""

    external : bool
    """"""

    takeFocus : bool
    """"""

    selection : Range
    """"""

    def __init__(self, uri, external, takeFocus, selection):
        self.uri = uri
        self.external = external
        self.takeFocus = takeFocus
        self.selection = selection

class ShowDocumentResult:
    """"""

    success : bool
    """"""

    def __init__(self, success):
        self.success = success

class TaskFinishedInfo:
    """"""

    def __init__(self, ):
        pass


class TaskStartedInfo:
    """"""

    def __init__(self, ):
        pass


KEY_DATA_CLASSES = { "ExampleDesc": ExampleDesc,"ProofMacroDesc": ProofMacroDesc,"ProofScriptCommandDesc": ProofScriptCommandDesc,"TraceValue": TraceValue,"SetTraceParams": SetTraceParams,"EnvironmentId": EnvironmentId,"ProofId": ProofId,"NodeId": NodeId,"List": List,"NodeDesc": NodeDesc,"StreategyOptions": StreategyOptions,"MacroStatistic": MacroStatistic,"ProofStatus": ProofStatus,"TreeNodeDesc": TreeNodeDesc,"TreeNodeId": TreeNodeId,"PrintOptions": PrintOptions,"NodeTextId": NodeTextId,"NodeTextDesc": NodeTextDesc,"TermActionId": TermActionId,"TermActionKind": TermActionKind,"TermActionDesc": TermActionDesc,"SortDesc": SortDesc,"FunctionDesc": FunctionDesc,"ContractId": ContractId,"ContractDesc": ContractDesc,"LoadParams": LoadParams,"ProblemDefinition": ProblemDefinition,"LogTraceParams": LogTraceParams,"MessageType": MessageType,"ShowMessageParams": ShowMessageParams,"ShowMessageRequestParams": ShowMessageRequestParams,"MessageActionItem": MessageActionItem,"Range": Range,"ShowDocumentParams": ShowDocumentParams,"ShowDocumentResult": ShowDocumentResult,"TaskFinishedInfo": TaskFinishedInfo,"TaskStartedInfo": TaskStartedInfo }

