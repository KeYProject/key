# KeY compiler warning inventory

* generated: 2026-10-24T22:57:19.624260+00:00
* command: `./gradlew --console=plain testClasses --offline --rerun-tasks`

Total warnings: **1809** across **2** modules, in **14** categories.

## Summary by category

| category | count |
|---|---|
| deprecation | 834 |
| serial | 351 |
| this-escape | 310 |
| unchecked | 141 |
| rawtypes | 79 |
| auxiliaryclass | 48 |
| dangling-doc-comments | 13 |
| try | 13 |
| cast | 10 |
| overrides | 4 |
| lossy-conversions | 2 |
| varargs | 2 |
| overloads | 1 |
| static | 1 |

## Summary by module

| module | count |
|---|---|
| key.core | 1260 |
| key.ui | 549 |

## Details (grouped by category, module, file)

### deprecation (834)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/loader/JP2KeYConverter.java` — 43
  * `key.core/src/main/java/de/uka/ilkd/key/java/KeYJavaASTFactory.java` — 24
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/constraint/EqualityConstraint.java` — 22
  * `key.core/src/main/java/de/uka/ilkd/key/logic/BoundVariableTools.java` — 20
  * `key.core/src/main/java/de/uka/ilkd/key/logic/TermFactory.java` — 20
  * `key.core/src/main/java/de/uka/ilkd/key/proof/TermTacletAppIndex.java` — 19
  * `key.core/src/main/java/de/uka/ilkd/key/pp/PrettyPrinter.java` — 15
  * `key.core/src/main/java/de/uka/ilkd/key/logic/TermImpl.java` — 14
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/StatementBlock.java` — 13
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/JFunction.java` — 13
  * `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/WhileInvariantTransformer.java` — 13
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/AssumesInstantiator.java` — 13
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/LocalVariableDeclaration.java` — 12
  * `key.core/src/main/java/de/uka/ilkd/key/logic/ClashFreeSubst.java` — 12
  * `key.core/src/main/java/de/uka/ilkd/key/rule/SyntacticalReplaceVisitor.java` — 11
  * `key.core/src/main/java/de/uka/ilkd/key/smt/AbstractSMTTranslator.java` — 11
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/CompilationUnit.java` — 10
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ProgramSV.java` — 10
  * `key.core/src/main/java/de/uka/ilkd/key/nparser/builder/ExpressionBuilder.java` — 10
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/reference/MethodReference.java` — 9
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/JAbstractSortedOperator.java` — 9
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/FieldDeclaration.java` — 8
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/Operator.java` — 8
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/reference/ArrayReference.java` — 8
  * `key.core/src/main/java/de/uka/ilkd/key/logic/LabeledTermImpl.java` — 8
  * `key.core/src/main/java/de/uka/ilkd/key/rule/conditions/StaticMethodCondition.java` — 8
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/JavaDeclaration.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/MethodDeclaration.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/TypeDeclaration.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/reference/SpecialConstructorReference.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Exec.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Try.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/nparser/builder/FunctionPredicateBuilder.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/rule/QueryExpand.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/PositionedString.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/InheritanceSpecification.java` — 6
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/ParameterDeclaration.java` — 6
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/Throws.java` — 6
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/MethodBodyStatement.java` — 6
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ParametricFunctionDecl.java` — 6
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/IfInstantiationCachePool.java` — 6
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/ArrayInitializer.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Case.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Default.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/LoopInit.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Switch.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/java/loader/CreateArrayMethodBuilder.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/logic/equality/ProofIrrelevancyProperty.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/pp/LogicPrinter.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/rule/conditions/MayExpandMethodCondition.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/rule/match/vm/JavaListSVMatcher.java` — 5
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/IssueDialog.java` — 5
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/VariableDeclaration.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/For.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/ForUpdates.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/LoopStatement.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/java/visitor/ProgramReplaceVisitor.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ObserverFunction.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ProgramMethod.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/proof/OpReplacer.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/rule/AuxiliaryContractBuilders.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/rule/LightweightSyntacticalReplaceVisitor.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/rule/LoopInvariantBuiltInRuleApp.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/rule/conditions/TermLabelCondition.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/MethodCall.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/settings/ProofSettings.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/smt/newsmt2/QuantifierHandler.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/PositionedLabeledString.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/jml/translation/JMLSpecFactory.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/util/MiscTools.java` — 4
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/TextLineNumber.java` — 4
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/KeYProgModelInfo.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/InterfaceDeclaration.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/LabeledStatement.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/JOperatorSV.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ParametricFunctionInstance.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/Transformer.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/macros/FinishSymbolicExecutionUntilMergePointMacro.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/proof/ProgVarReplacer.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/rule/TacletApp.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/rule/UseOperationContractRule.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/rule/match/vm/JavaBinderMatcher.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/rule/match/vm/instructions/MatchTermLabelInstruction.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/InitArray.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/rule/tacletbuilder/TacletGenerator.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/settings/ProofIndependentSettings.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/smt/newsmt2/SMTTacletTranslator.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/jml/JMLInfoExtractor.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/definition/AbstractStrategyPropertyDefinition.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/definition/OneOfStrategyPropertyDefinition.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/definition/StrategySettingsDefinition.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/taclettranslation/assumptions/AssumptionGenerator.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/util/mergerule/MergeRuleUtils.java` — 3
  * `key.core/src/test/java/de/uka/ilkd/key/strategy/quantifierHeuristics/TestTriggersSet.java` — 3
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ProofScriptWorker.java` — 3
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/control/instantiation_model/TacletFindModel.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/control/instantiation_model/TacletInstantiationModel.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/ClassDeclaration.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/ConstructorDeclaration.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/LogicFunctionalOperator.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/New.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/reference/SuperConstructorReference.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/reference/ThisConstructorReference.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/visitor/ProgramContextAdder.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/ldt/HeapLDT.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/logic/LexPathOrdering.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/logic/WaryClashFreeSubst.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/IProgramMethod.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ModalOperatorSV.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/pp/SequentViewLogicPrinter.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/proof/init/FunctionalOperationContractPO.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/rule/EqualityModuloProofIrrelevancy.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/rule/WhileInvariantRule.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/rule/match/vm/instructions/BindVariablesInstruction.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/rule/match/vm/instructions/JavaDLMatchVMInstructionSet.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/MultipleVarDecl.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/WhileLoopTransformation.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/AbstractPropertiesSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/ChoiceSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/FeatureSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/GeneralSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/LemmaGeneratorSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/NewSMTTranslationSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/ProofDependentSMTSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/ProofIndependentSMTSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/StrategyPresetsSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/StrategySettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/TermLabelSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/smt/SMTObjTranslator.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/smt/newsmt2/DefinedSymbolsHandler.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/AuxiliaryContract.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/ContractFactory.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/TwoSidedMatching.java` — 2
  * `key.core/src/test/java/de/uka/ilkd/key/util/TestLinkedHashMapWrapper.java` — 2
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/WindowUserInterfaceControl.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SendFeedbackAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToolTipOptionsAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/notification/actions/GeneralFailureJTextPaneDisplay.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/classic/TacletMatchCompletionDialog.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/utilities/BracketMatchingTextArea.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/utilities/ErrorMarkPainter.java` — 2
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/JavaService.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/ContextStatementBlock.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/Declaration.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/JavaNonTerminalProgramElement.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/ccatch/CcatchReturnValParameterDeclaration.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/Extends.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/Implements.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/BinaryAssignment.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/ParenthesizedExpression.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/UnaryAssignment.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/BinaryOperator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/Conditional.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/DLEmbeddedExpression.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/Instanceof.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/NewArray.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/TypeCast.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/TypeOperator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/UnaryOperator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/reference/MethodOrConstructorReference.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/IForUpdates.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/ILoopInit.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/LoopScopeBlock.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/MethodFrame.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/SynchronizedBlock.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/loader/JP2KeYTypeConverter.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/ConstantStringExpressionEvaluator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/visitor/CreatingASTVisitor.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/visitor/ProgVarReplaceVisitor.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/visitor/UndeclaredProgramVariableCollector.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/MethodStackInfo.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/ProgramPrefix.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/label/LabelCollection.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/IObserverFunction.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/init/AbstractOperationPO.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/init/KeYUserProblemFile.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/io/IntermediateProofReplayer.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/io/KeYFile.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/io/consistency/DiskFileRepo.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/LoopScopeInvariantRule.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/ObserverToUpdateRule.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/OneStepSimplifier.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/conditions/ApplyUpdateOnRigidCondition.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/conditions/NewLocalVarsCondition.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/label/OriginTermLabelRefactoring.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/merge/CloseAfterMerge.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/ArrayPostDecl.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/ConstructorCall.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/EvaluateArgs.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/ExpandMethodBody.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/InitArrayCreation.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/tacletbuilder/TacletPrefixBuilder.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/DependencyContractCommand.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/TermWithHoles.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/smt/newsmt2/FloatHandler.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/FunctionalOperationContractImpl.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/QueryAxiom.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/jml/JMLSpecExtractor.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/njml/JmlFacade.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/TriggersSet.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/constraint/ConstraintAwareSyntacticalReplaceVisitor.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/theory/EqualityTheorySupport.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/theory/HeapArrayTheorySupport.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/termgenerator/SuperTermGenerator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/termgenerator/TriggeredInstantiations.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/taclettranslation/assumptions/GenericTranslator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/taclettranslation/lemma/DefaultLemmaGenerator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/util/parsing/BuildingException.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/scripts/ProofScriptParserTest.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/strategy/TieBreakComparatorPropertyTest.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ProofMacroMenu.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/EditSourceFileAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/KeYProjectHomepageAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ProofManagementAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/notification/events/ExceptionFailureEvent.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/DefaultSettingsProvider.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/SettingsUi.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/utilities/CurrentLineHighlighter.java` — 1

### serial (351)

* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/CurrentGoalViewMenu.java` — 23
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/originlabels/OriginTermLabelVisualizer.java` — 12
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/prooftree/ProofTreePopupFactory.java` — 12
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/InvariantConfigurator.java` — 9
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/KeyboardTacletExtension.java` — 9
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/control/instantiation_model/TacletFindModel.java` — 7
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/InfoView.java` — 7
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/control/instantiation_model/TacletAssumesModel.java` — 6
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/TaskTree.java` — 6
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/SourceView.java` — 6
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/AssumesSelectionPanel.java` — 6
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/KeYFileChooserBookmarkPanel.java` — 5
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/LogView.java` — 5
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/lemmatagenerator/ItemChooser.java` — 5
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/mergerule/MergePartnerSelectionDialog.java` — 5
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/InsertionTacletBrowserMenuItem.java` — 5
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/prooftree/GUIProofTreeModel.java` — 5
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/utilities/HeapStatusExt.java` — 5
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/util/parsing/BuildingException.java` — 4
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ProofManagementDialog.java` — 4
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/TermLabelMenu.java` — 4
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/colors/ColorSettingsProvider.java` — 4
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/InnerNodeView.java` — 4
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/SequentViewMenu.java` — 4
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/plugins/javac/JavacSettings.java` — 4
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/SettingsDialog.java` — 4
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/SourceHighlightDocument.java` — 4
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/util/parsing/SyntaxErrorReporter.java` — 3
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ExampleChooser.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/IssueDialog.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/KeYFileChooserLoadingOptions.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/StrategySelectionView.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/RunAllProofsAction.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SettingsTreeModel.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ShowProofStatistics.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/configuration/ChoiceSelector.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/keyshortcuts/ShortcutSettings.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/JavaDocument.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/ResultPreviewPanel.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/SVInstantiationPanel.java` — 3
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/ConvertException.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/loader/JavaBuildingExceptions.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/parser/ParserException.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/proof/SVInstantiationExceptionWithPosition.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/proof/io/ProblemLoaderException.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/proof/mgt/ProofEnvironmentEvent.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/rule/tacletbuilder/TacletBuilder.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/translation/SLTranslationException.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/util/parsing/BuildingExceptions.java` — 2
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ApplyTacletDialog.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ClassTree.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ContractSelectionPanel.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/RecentFileMenu.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/AutoModeAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/EditSourceFileAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/MacroKeyBinding.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SelectionBackAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SelectionForwardAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SendFeedbackAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ShowActiveSettingsAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToggleSourceViewTooltipAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/join/JoinDialog.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/lemmatagenerator/LemmaSelectionDialog.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/lemmatagenerator/LoadUserTacletsDialog.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/plugins/action_history/UndoHistoryButton.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/proofdiff/ProofDiffFrame.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/prooftree/ProofTreeSearchBar.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/FeatureSettingsPanel.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/TacletOptionsSettings.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/DropdownSelectionButton.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/settings/NewTranslationOptions.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/MatchInfoPanel.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/classic/TacletMatchCompletionDialog.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/utilities/BracketMatchingTextArea.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/utilities/CheckedUserInput.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/proof/mgt/ProofAggregateTask.java` — 2
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/transformations/EvaluationException.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/sort/GenericSupersortException.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/MissingSortException.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/ProofNodeDescription.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/SVRigidnessException.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/SortMismatchException.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/init/FinalFieldCodeValidator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/ScriptException.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/meta/ArgumentRequiredException.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/meta/ConversionException.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/meta/InjectionException.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/meta/InjectionReflectionException.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/meta/UnknownArgumentException.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/StrategyProperties.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/util/mergerule/MergeRuleUtils.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/AuxiliaryContractSelectionPanel.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/KeYFileChooser.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/MainStatusLine.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/MaxRuleAppSlider.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/NodeInfoVisualizer.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ProofSelectionDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/CreateGithubIssueAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ExitMainAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/GotoNodeAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/HidePackagePrefixToggleAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/MacroAutomationAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/MinimizeInteraction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/OpenFileAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/OpenSingleJavaFileAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/PrettyPrintToggleAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ProofScriptFromFileAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ProofScriptInputAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ShowKnownTypesAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ShowUsedContractsAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SyntaxHighlightingToggleAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToggleProofTreeTooltipAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToggleSequentViewTooltipAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/UnicodeToggleAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/extension/ExtensionManager.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/extension/impl/HeatmapExt.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/extension/impl/TestExtension.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/help/HelpFacade.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/mergerule/predicateabstraction/AbstractionPredicatesChoiceDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/mergerule/predicateabstraction/ObservableArrayList.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/DefaultTacletMenuItem.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/EmptySequent.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/SequentViewDock.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/originlabels/ShowOriginAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/originlabels/ToggleTermOriginTrackingAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/plugins/javac/JavacSettingsProvider.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/InvalidSettingsInputException.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/ParallelProverSettingsProvider.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/SettingsManager.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/SimpleSettingsPanel.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/StandardUISettings.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/settings/SMTSettingsProvider.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/settings/SolverOptions.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/settings/TranslationOptions.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/soundiness/SoundinessDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/SourceViewFrame.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/TacletMatchDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/classic/ApplyTacletDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/classic/TacletIfSelectionDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/proof/mgt/BasicTask.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/proof/mgt/EnvNode.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/proof/mgt/TaskTreeModel.java` — 1

### this-escape (310)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/settings/ViewSettings.java` — 33
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/utilities/BracketMatchingTextArea.java` — 12
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/utilities/LexerHighlighter.java` — 8
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/TypeDeclaration.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Exec.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Try.java` — 4
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/AuxiliaryContractConfigurator.java` — 4
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ContractConfigurator.java` — 4
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/lemmatagenerator/LoadUserTacletsDialog.java` — 4
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/control/instantiation_model/TacletInstantiationModel.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/StatementBlock.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/MethodDeclaration.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/LabeledStatement.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/SynchronizedBlock.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/rule/BoundUniquenessChecker.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/EngineState.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/settings/FeatureSettings.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/StringStrategy.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/util/LinkedHashMap.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/util/LinkedHashMapWrapper.java` — 3
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/plugins/javac/JavacSettings.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/proofdiff/ProofDiffFrame.java` — 3
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/control/DefaultUserInterfaceControl.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/abstraction/KeYJavaType.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/literal/LongLiteral.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/Instanceof.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/reference/FieldReference.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/reference/MethodReference.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/MethodFrame.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/ProofSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/IntegerStrategy.java` — 2
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/NodeInfoVisualizer.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/EditSourceFileAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SettingsTreeModel.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/docking/DynamicCMenu.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/mergerule/MergePartnerSelectionDialog.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/mergerule/predicateabstraction/AbstractionPredicatesChoiceDialog.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/SequentViewDock.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/SimpleTacletSelectionMenu.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/plugins/action_history/UndoHistoryButton.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/soundiness/SoundinessDialog.java` — 2
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/control/AbstractUserInterfaceControl.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/control/instantiation_model/TacletAssumesModel.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/EnumClassDeclaration.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/visitor/ProgramVariableCollector.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/ldt/PermissionLDT.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/AbstractTermTransformer.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/JModality.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ProgramVariable.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/nparser/builder/ExpressionBuilder.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/pp/AbbrevMap.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/Node.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/Statistics.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/init/AbstractProfile.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/init/JavaProfile.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/io/AbstractProblemLoader.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/BlockContractExternalBuiltInRuleApp.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/BlockContractInternalBuiltInRuleApp.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/LoopContractExternalBuiltInRuleApp.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/LoopContractInternalBuiltInRuleApp.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/LoopInvariantBuiltInRuleApp.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/merge/CloseAfterMergeRuleBuiltInRuleApp.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/ProofScriptEngine.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/settings/AbstractSettings.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/smt/newsmt2/MasterHandler.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/njml/JmlMarkerDecision.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/FOLStrategy.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/FocussedBreakpointRuleApplicationManager.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/FocussedRuleApplicationManager.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/JavaCardDLStrategy.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/LocSetStrategy.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/ModularJavaDLStrategy.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/SetStrategy.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/SymExStrategy.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/taclettranslation/assumptions/AssumptionGenerator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/util/InfFlowProgVarRenamer.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ApplyTacletDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/AuxiliaryContractSelectionPanel.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ClassTree.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ContractSelectionPanel.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/HeatmapOptionsDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/InfoView.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/KeYFileChooserBookmarkPanel.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/KeYFileChooserLoadingOptions.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/MaxRuleAppSlider.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ProofMacroMenu.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/SelectionHistory.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/ShortUniqueFileNames.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/TableRowResizer.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/TaskTree.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/AboutAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/AutoModeAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/AutoSave.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/CopyToClipboardAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/CreateGithubIssueAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/DecreaseFontSizeAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/EnsureSourceConsistencyToggleAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ExitMainAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/GotoNodeAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/HeatmapSettingsAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/HeatmapToggleAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/IncreaseFontSizeAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/KeYProjectHomepageAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/LemmaGenerationAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/LemmaGenerationBatchModeAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/LicenseAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/MacroAutomationAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/MenuSendFeedackAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/MinimizeInteraction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/OpenFileAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/OpenSingleJavaFileAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/PrettyPrintToggleAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/QuickLoadAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/RightMouseClickToggleAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/RunAllProofsAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SMTInvokeAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SMTOptionsAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SearchInProofTreeAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SearchInSequentAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SearchModeChangeAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SearchNextAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SearchPreviousAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SelectionBackAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SelectionForwardAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SendFeedbackAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ShowActiveSettingsAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ShowActiveTactletOptionsAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ShowKnownTypesAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ShowProofStatistics.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ShowSoundinessAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ShowUsedContractsAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SyntaxHighlightingToggleAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SystemInfoAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/TacletOptionsAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/TermLabelMenu.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToggleConfirmExitAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToggleProofTreeTooltipAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToggleSequentViewTooltipAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToggleSourceViewTooltipAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToolTipOptionsAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/UnicodeToggleAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/colors/ColorSettingsProvider.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/configuration/ChoiceSelector.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/configuration/ViewSelector.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/extension/ExtensionManager.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/extension/impl/ExtensionSettings.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/fonticons/ShowIcons.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/join/JoinDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/join/JoinMenuItem.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/join/SequentViewer.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/keyshortcuts/ShortcutSettings.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/lemmatagenerator/LemmaSelectionDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/mergerule/MergeRuleMenuItem.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/EmptySequent.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/InsertionTacletBrowserMenuItem.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/SequentHideWarningBorder.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/notification/ExceptionFailureNotification.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/notification/GeneralFailureNotification.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/notification/GeneralInformationNotification.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/notification/NotificationManager.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/notification/ProofClosedNotification.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/originlabels/ShowOriginAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/originlabels/ToggleOriginHighlightAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/originlabels/ToggleTermOriginTrackingAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/plugins/action_history/ActionHistoryExtension.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/plugins/javac/JavacSettingsProvider.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/DefaultSettingsProvider.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/FeatureSettingsPanel.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/ParallelProverSettingsProvider.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/SettingsDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/SettingsManager.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/SettingsUi.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/SimpleSettingsPanel.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/StandardUISettings.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/TacletOptionsSettings.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/DropdownSelectionButton.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/OptionContentNode.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/settings/SMTSettingsProvider.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/settings/TacletTranslationOptions.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/JavaDocument.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/SourceHighlightDocument.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/SourceViewFrame.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/TextLineNumber.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/AssumesSelectionPanel.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/ExpandableText.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/MatchInfoPanel.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/ResponsiveSplit.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/ResultPreviewPanel.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/SVInstantiationPanel.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/TacletMatchDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/classic/TacletIfSelectionDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/tacletmatch/classic/TacletMatchCompletionDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/utilities/CheckedUserInput.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/utilities/ClickableMessageBox.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/utilities/ClosableTabComponent.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/utilities/StdDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/ui/ConsoleUserInterfaceControl.java` — 1

### unchecked (141)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/logic/TermImpl.java` — 13
  * `key.core/src/main/java/de/uka/ilkd/key/macros/StrategyProofMacro.java` — 8
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/StaticFeatureCollection.java` — 6
  * `key.core/src/test/java/de/uka/ilkd/key/rule/TestSchemaModalOperators.java` — 6
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/DependencyContractCompletion.java` — 5
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/loader/JP2KeYConverter.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/rule/OneStepSimplifierRuleApp.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/util/Union.java` — 4
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/LoopInvariantRuleCompletion.java` — 4
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/macros/DefaultAutoMacro.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/rule/UseDependencyContractApp.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/settings/AbstractPropertiesSettings.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/constraint/EqualityConstraint.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/util/HelperClassForTests.java` — 3
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/extension/impl/KeYGuiExtensionFacade.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/settings/SettingsPanel.java` — 3
  * `key.ui/src/main/java/org/key_project/util/java/SwingUtil.java` — 3
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/proof/init/AbstractProfile.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/proof/init/JavaProfile.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/rule/LoopContractInternalRule.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/rule/Taclet.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/AdditionalRulesStrategy.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/AutoCommand.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/smt/SMTRule.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/njml/Translator.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/TransformationPipelineServices.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/ldt/AbstractLDT.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/equality/ProofIrrelevancyProperty.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/equality/TermLabelsProperty.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/label/LabelCollection.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ProgramSV.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/nparser/KeyAst.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/nparser/builder/DeclarationBuilder.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/nparser/builder/DefaultBuilder.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/nparser/builder/FunctionPredicateBuilder.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/ProgVarReplacer.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/prover/impl/PerfScope.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/AbstractLoopInvariantRule.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/AntecTaclet.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/BlockContractExternalRule.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/BuiltInRule.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/FindTaclet.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/NoFindTaclet.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/ObserverToUpdateRule.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/OneStepSimplifier.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/QueryExpand.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/RewriteTaclet.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/SuccTaclet.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/tacletbuilder/AntecTacletBuilder.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/tacletbuilder/RewriteTacletBuilder.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/tacletbuilder/SuccTacletBuilder.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/tacletbuilder/TacletGenerator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/tacletbuilder/TacletGoalTemplate.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/SetCommand.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/meta/ValueInjector.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/smt/lang/SMTTerm.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/smt/newsmt2/FloatRemainderHandler.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/smt/newsmt2/QuantifierHandler.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/smt/newsmt2/SMTHandlerServices.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/smt/newsmt2/SeqDefHandler.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/FocussedBreakpointRuleApplicationManager.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/FocussedRuleApplicationManager.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/QueueRuleApplicationManager.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/feature/ComprehendedSumFeature.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/feature/ImplicitCastNecessary.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/constraint/ConstraintAwareSyntacticalReplaceVisitor.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/util/LinkedHashMapWrapper.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/BlockContractExternalCompletion.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/BlockContractInternalCompletion.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/LoopContractExternalCompletion.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/LoopContractInternalCompletion.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/WindowUserInterfaceControl.java` — 1

### rawtypes (79)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/KeYJavaASTFactory.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/rule/AbstractLoopInvariantRule.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/rule/UseDependencyContractApp.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/macros/StrategyProofMacro.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/rule/LoopContractInternalRule.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/rule/QueryExpand.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/rule/UseDependencyContractRule.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/logic/TermImpl.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/macros/DefaultAutoMacro.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/proof/init/AbstractOperationPO.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/proof/init/FinalFieldCodeValidator.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/rule/ObserverToUpdateRule.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/rule/UseOperationContractRule.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/EvaluateArgs.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/AutoCommand.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/StaticFeatureCollection.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/JavaAstUtils.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/BinaryAssignment.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/ConstantStringExpressionEvaluator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/PrepareObjectBuilder.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/TransformationPipelineServices.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/ClashFreeSubst.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/WaryClashFreeSubst.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/prover/impl/PerfScope.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/AbstractBlockContractRule.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/AuxiliaryContractBuilders.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/BlockContractExternalRule.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/LoopInvariantBuiltInRuleApp.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/OneStepSimplifier.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/OneStepSimplifierRuleApp.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/Taclet.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/WhileInvariantRule.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/tacletbuilder/TacletPrefixBuilder.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/AdditionalRulesStrategy.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/DependencyContractCommand.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/scripts/SetCommand.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/TacletAppContainer.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/TriggersSet.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/BlockContractExternalCompletion.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/BlockContractInternalCompletion.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/DependencyContractCompletion.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/InvariantConfigurator.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/LoopContractExternalCompletion.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/LoopContractInternalCompletion.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/LoopInvariantRuleCompletion.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SettingsTreeModel.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/extension/impl/Extension.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/extension/impl/KeYGuiExtensionFacade.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/originlabels/OriginTermLabelsExt.java` — 1

### auxiliaryclass (48)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/IntegerStrategy.java` — 46
  * `key.core/src/main/java/de/uka/ilkd/key/taclettranslation/lemma/DefaultLemmaGenerator.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/fonticons/IconFontProvider.java` — 1

### dangling-doc-comments (13)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/logic/LexPathOrdering.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/proof/TermTacletAppIndexCacheSet.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/logic/BoundVariableTools.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/sort/GenericSort.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/inst/GenericSortException.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/settings/PathConfig.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/theory/IntegerTheorySupport.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/tiebreak/PolarityOccurrenceTieBreak.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/HeatmapOptionsDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/WindowUserInterfaceControl.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/prooftree/GUIProofTreeNode.java` — 1

### try (13)

* **key.core**
  * `key.core/src/test/java/de/uka/ilkd/key/prover/mt/ListenerSuspensionTest.java` — 6
  * `key.core/src/test/java/de/uka/ilkd/key/prover/mt/MergeRuleMultiThreadGuardTest.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/control/KeYEnvironment.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/prover/impl/ParallelProver.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/util/ZipFileCollection.java` — 1

### cast (10)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/settings/StrategyPresetsSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/StrategySettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/ldt/HeapLDT.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/JavaLogger.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/TacletSchemaVariableCollector.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/CostReuse.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/ModularJavaDLStrategy.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/strategy/QueueRuleApplicationManagerParkingLocalityTest.java` — 1

### overrides (4)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ProgramMethod.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/smt/SMTSolverResult.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/smt/model/Heap.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/constraint/Metavariable.java` — 1

### lossy-conversions (2)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/smt/ModelExtractor.java` — 2

### varargs (2)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/StaticFeatureCollection.java` — 2

### overloads (1)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/StaticFeatureCollection.java` — 1

### static (1)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/proof/io/OutputStreamProofSaver.java` — 1

