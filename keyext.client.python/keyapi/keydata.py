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

class ProofScriptCommandDesc:
    """"""

    macroId : str
    """"""

    documentation : str
    """"""

    def __init__(self, macroId, documentation):
        self.macroId = macroId
        self.documentation = documentation

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

    description : str
    """"""

    def __init__(self, nodeid, branchLabel, scriptRuleApplication, children, description):
        self.nodeid = nodeid
        self.branchLabel = branchLabel
        self.scriptRuleApplication = scriptRuleApplication
        self.children = children
        self.description = description

class StrategyOptions:
    """"""

    method : str
    """"""

    dep : str
    """"""

    query : str
    """"""

    nonLinArith : str
    """"""

    stopMode : str
    """"""

    maxSteps : int
    """"""

    def __init__(self, method, dep, query, nonLinArith, stopMode, maxSteps):
        self.method = method
        self.dep = dep
        self.query = query
        self.nonLinArith = nonLinArith
        self.stopMode = stopMode
        self.maxSteps = maxSteps

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


KEY_DATA_CLASSES = { "org.keyproject.key.api.remoteapi.ExampleDesc": ExampleDesc,"org.keyproject.key.api.data.ProofScriptCommandDesc": ProofScriptCommandDesc,"org.keyproject.key.api.data.ProofMacroDesc": ProofMacroDesc,"org.keyproject.key.api.data.TraceValue": TraceValue,"org.keyproject.key.api.remoteapi.ServerManagement$SetTraceParams": SetTraceParams,"org.keyproject.key.api.data.KeyIdentifications$EnvironmentId": EnvironmentId,"org.keyproject.key.api.data.KeyIdentifications$ProofId": ProofId,"org.keyproject.key.api.data.KeyIdentifications$NodeId": NodeId,"java.util.List": List,"org.keyproject.key.api.data.NodeDesc": NodeDesc,"org.keyproject.key.api.data.StrategyOptions": StrategyOptions,"org.keyproject.key.api.data.MacroStatistic": MacroStatistic,"org.keyproject.key.api.data.ProofStatus": ProofStatus,"org.keyproject.key.api.data.TreeNodeDesc": TreeNodeDesc,"org.keyproject.key.api.data.KeyIdentifications$TreeNodeId": TreeNodeId,"org.keyproject.key.api.remoteapi.PrintOptions": PrintOptions,"org.keyproject.key.api.data.KeyIdentifications$NodeTextId": NodeTextId,"org.keyproject.key.api.data.NodeTextDesc": NodeTextDesc,"org.keyproject.key.api.data.KeyIdentifications$TermActionId": TermActionId,"org.keyproject.key.api.data.TermActionKind": TermActionKind,"org.keyproject.key.api.data.TermActionDesc": TermActionDesc,"org.keyproject.key.api.data.SortDesc": SortDesc,"org.keyproject.key.api.data.FunctionDesc": FunctionDesc,"org.keyproject.key.api.data.KeyIdentifications$ContractId": ContractId,"org.keyproject.key.api.data.ContractDesc": ContractDesc,"org.keyproject.key.api.data.LoadParams": LoadParams,"org.keyproject.key.api.data.ProblemDefinition": ProblemDefinition,"org.keyproject.key.api.remoteclient.LogTraceParams": LogTraceParams,"org.keyproject.key.api.remoteclient.MessageType": MessageType,"org.keyproject.key.api.remoteclient.ShowMessageParams": ShowMessageParams,"org.keyproject.key.api.remoteclient.ShowMessageRequestParams": ShowMessageRequestParams,"org.keyproject.key.api.remoteclient.MessageActionItem": MessageActionItem,"de.uka.ilkd.key.pp.Range": Range,"org.keyproject.key.api.remoteclient.ShowDocumentParams": ShowDocumentParams,"org.keyproject.key.api.remoteclient.ShowDocumentResult": ShowDocumentResult,"org.keyproject.key.api.data.TaskFinishedInfo": TaskFinishedInfo,"org.keyproject.key.api.data.TaskStartedInfo": TaskStartedInfo }

KEY_DATA_CLASSES_REV = { "ExampleDesc": "org.keyproject.key.api.remoteapi.ExampleDesc","ProofScriptCommandDesc": "org.keyproject.key.api.data.ProofScriptCommandDesc","ProofMacroDesc": "org.keyproject.key.api.data.ProofMacroDesc","TraceValue": "org.keyproject.key.api.data.TraceValue","SetTraceParams": "org.keyproject.key.api.remoteapi.ServerManagement$SetTraceParams","EnvironmentId": "org.keyproject.key.api.data.KeyIdentifications$EnvironmentId","ProofId": "org.keyproject.key.api.data.KeyIdentifications$ProofId","NodeId": "org.keyproject.key.api.data.KeyIdentifications$NodeId","List": "java.util.List","NodeDesc": "org.keyproject.key.api.data.NodeDesc","StrategyOptions": "org.keyproject.key.api.data.StrategyOptions","MacroStatistic": "org.keyproject.key.api.data.MacroStatistic","ProofStatus": "org.keyproject.key.api.data.ProofStatus","TreeNodeDesc": "org.keyproject.key.api.data.TreeNodeDesc","TreeNodeId": "org.keyproject.key.api.data.KeyIdentifications$TreeNodeId","PrintOptions": "org.keyproject.key.api.remoteapi.PrintOptions","NodeTextId": "org.keyproject.key.api.data.KeyIdentifications$NodeTextId","NodeTextDesc": "org.keyproject.key.api.data.NodeTextDesc","TermActionId": "org.keyproject.key.api.data.KeyIdentifications$TermActionId","TermActionKind": "org.keyproject.key.api.data.TermActionKind","TermActionDesc": "org.keyproject.key.api.data.TermActionDesc","SortDesc": "org.keyproject.key.api.data.SortDesc","FunctionDesc": "org.keyproject.key.api.data.FunctionDesc","ContractId": "org.keyproject.key.api.data.KeyIdentifications$ContractId","ContractDesc": "org.keyproject.key.api.data.ContractDesc","LoadParams": "org.keyproject.key.api.data.LoadParams","ProblemDefinition": "org.keyproject.key.api.data.ProblemDefinition","LogTraceParams": "org.keyproject.key.api.remoteclient.LogTraceParams","MessageType": "org.keyproject.key.api.remoteclient.MessageType","ShowMessageParams": "org.keyproject.key.api.remoteclient.ShowMessageParams","ShowMessageRequestParams": "org.keyproject.key.api.remoteclient.ShowMessageRequestParams","MessageActionItem": "org.keyproject.key.api.remoteclient.MessageActionItem","Range": "de.uka.ilkd.key.pp.Range","ShowDocumentParams": "org.keyproject.key.api.remoteclient.ShowDocumentParams","ShowDocumentResult": "org.keyproject.key.api.remoteclient.ShowDocumentResult","TaskFinishedInfo": "org.keyproject.key.api.data.TaskFinishedInfo","TaskStartedInfo": "org.keyproject.key.api.data.TaskStartedInfo" }

