## Types
### Type: ContractDesc
```
type ContractDesc {
 	contractId : ContractId
	displayName : STRING
	htmlText : STRING
	name : STRING
	plainText : STRING
	typeName : STRING
}
```

### Type: ContractId
```
type ContractId {
 	contractId : INT
	envId : EnvironmentId
}
```

### Type: EnvironmentId
```
type EnvironmentId {
 	envId : STRING
}
```

### Type: ExampleDesc
```
type ExampleDesc {
 	description : STRING
	name : STRING
}
```

### Type: FunctionDesc
```
type FunctionDesc {
 	argSorts : List
	name : STRING
	retSort : SortDesc
	rigid : BOOL
	skolemConstant : BOOL
	sort : STRING
	unique : BOOL
}
```

### Type: List
```
type List {
 
}
```

### Type: LoadParams
```
type LoadParams {
 	bootClassPath : STRING
	classPath : List
	includes : List
	javaFile : STRING
	keyFile : STRING
}
```

### Type: LogTraceParams
```
type LogTraceParams {
 	messag : STRING
	verbose : STRING
}
```

### Type: MessageActionItem
```
type MessageActionItem {
 	title : STRING
}
```

### Type: MessageType
```
enum MessageType { Unused, Error, Warning, Info, Log, Debug }
```

### Type: NodeId
```
type NodeId {
 	nodeId : INT
	proofId : ProofId
}
```

### Type: NodeTextDesc
```
type NodeTextDesc {
 	id : NodeTextId
	result : STRING
}
```

### Type: NodeTextId
```
type NodeTextId {
 	nodeId : NodeId
	nodeTextId : INT
}
```

### Type: PrintOptions
```
type PrintOptions {
 	indentation : INT
	pure : BOOL
	termLabels : BOOL
	unicode : BOOL
	width : INT
}
```

### Type: ProblemDefinition
```
type ProblemDefinition {
 	antecTerms : List
	functions : List
	predicates : List
	sorts : List
	succTerms : List
}
```

### Type: ProofId
```
type ProofId {
 	env : EnvironmentId
	proofId : STRING
}
```

### Type: ProofMacroDesc
```
type ProofMacroDesc {
 	category : STRING
	description : STRING
	name : STRING
	scriptCommandName : STRING
}
```

### Type: ProofScriptCommandDesc
```
type ProofScriptCommandDesc {
 
}
```

### Type: Range
```
type Range {
 	end : INT
	start : INT
}
```

### Type: SetTraceParams
```
type SetTraceParams {
 	value : TraceValue
}
```

### Type: ShowDocumentParams
```
type ShowDocumentParams {
 	external : BOOL
	selection : Range
	takeFocus : BOOL
	uri : STRING
}
```

### Type: ShowDocumentResult
```
type ShowDocumentResult {
 	success : BOOL
}
```

### Type: ShowMessageParams
```
type ShowMessageParams {
 	message : STRING
	type : MessageType
}
```

### Type: ShowMessageRequestParams
```
type ShowMessageRequestParams {
 	actions : List
	message : STRING
	type : MessageType
}
```

### Type: SortDesc
```
type SortDesc {
 	anAbstract : BOOL
	documentation : STRING
	extendsSorts : List
	s : STRING
	string : STRING
}
```

### Type: TaskFinishedInfo
```
type TaskFinishedInfo {
 
}
```

### Type: TaskStartedInfo
```
type TaskStartedInfo {
 
}
```

### Type: TermActionDesc
```
type TermActionDesc {
 	category : STRING
	commandId : TermActionId
	description : STRING
	displayName : STRING
	kind : TermActionKind
}
```

### Type: TermActionId
```
type TermActionId {
 	id : STRING
	nodeId : NodeId
	pio : STRING
}
```

### Type: TermActionKind
```
enum TermActionKind { BuiltIn, Script, Macro, Taclet }
```

### Type: TraceValue
```
enum TraceValue { Off, Message, All }
```

### Type: TreeNodeDesc
```
type TreeNodeDesc {
 
}
```

### Type: TreeNodeId
```
type TreeNodeId {
 	id : STRING
}
```

## Endpoints
### client/logTrace (`server ~~> client`) 

```
Client.client/logTrace( params : LogTraceParams ) **async**
```


### client/sayHello (`server ~~> client`) 

```
Client.client/sayHello( e : STRING ) **async**
```


### client/showDocument (`server -> client`) 

```
Client.client/showDocument( params : ShowDocumentParams ) -> ShowDocumentResult
```


### client/sm (`server ~~> client`) 

```
Client.client/sm( params : ShowMessageParams ) **async**
```


### client/userResponse (`server -> client`) 

```
Client.client/userResponse( params : ShowMessageRequestParams ) -> MessageActionItem
```


### env/contracts (`client -> server`) 

```
Server.env/contracts( env : EnvironmentId ) -> ContractDesc[]
```


### env/functions (`client -> server`) 

```
Server.env/functions( env : EnvironmentId ) -> FunctionDesc[]
```


### env/openContract (`client -> server`) 

```
Server.env/openContract( contractId : ContractId ) -> ProofId
```


### env/sorts (`client -> server`) 

```
Server.env/sorts( env : EnvironmentId ) -> SortDesc[]
```


### examples/list (`client -> server`) 

```
Server.examples/list(  ) -> ExampleDesc[]
```


### goal/actions (`client -> server`) 

```
Server.goal/actions( id : NodeTextId, pos : INT ) -> TermActionDesc[]
```


### goal/apply_action (`client -> server`) 

```
Server.goal/apply_action( id : TermActionId ) -> TermActionDesc[]
```


### goal/free (`client ~~> server`) 

```
Server.goal/free( id : NodeTextId ) **async**
```


### goal/print (`client -> server`) 

```
Server.goal/print( id : NodeId, options : PrintOptions ) -> NodeTextDesc
```


### loading/load (`client -> server`) 

```
Server.loading/load( params : LoadParams ) -> either<a,b>
```


### loading/loadExample (`client -> server`) 

```
Server.loading/loadExample( id : STRING ) -> ProofId
```


### loading/loadKey (`client -> server`) 

```
Server.loading/loadKey( content : STRING ) -> ProofId
```


### loading/loadProblem (`client -> server`) 

```
Server.loading/loadProblem( problem : ProblemDefinition ) -> ProofId
```


### loading/loadTerm (`client -> server`) 

```
Server.loading/loadTerm( term : STRING ) -> ProofId
```


### meta/available_macros (`client -> server`) 

```
Server.meta/available_macros(  ) -> ProofMacroDesc[]
```


### meta/available_script_commands (`client -> server`) 

```
Server.meta/available_script_commands(  ) -> ProofScriptCommandDesc[]
```


### meta/version (`client -> server`) 

```
Server.meta/version(  ) -> STRING
```


### proofTree/children (`client -> server`) 

```
Server.proofTree/children( proof : ProofId, nodeId : TreeNodeId ) -> TreeNodeDesc[]
```


### proofTree/root (`client -> server`) 

```
Server.proofTree/root( id : ProofId ) -> TreeNodeDesc
```


### proofTree/subtree (`client -> server`) 

```
Server.proofTree/subtree( proof : ProofId, nodeId : TreeNodeId ) -> TreeNodeDesc[]
```


### server/exit (`client ~~> server`) 

```
Server.server/exit(  ) **async**
```


### server/setTrace (`client ~~> server`) 

```
Server.server/setTrace( params : SetTraceParams ) **async**
```


### server/shutdown (`client -> server`) 

```
Server.server/shutdown(  ) -> BOOL
```

