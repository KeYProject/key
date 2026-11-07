# KeY compiler warning inventory

* generated: 2026-11-07T11:49:21.205926+00:00
* command: `./gradlew --console=plain testClasses --offline --rerun-tasks`

Total warnings: **870** across **8** modules, in **5** categories.

## Summary by category

| category | count |
|---|---|
| deprecation | 815 |
| other | 46 |
| try | 5 |
| unchecked | 3 |
| cast | 1 |

## Summary by module

| module | count |
|---|---|
| key.core | 807 |
| key.ncore | 23 |
| key.ncore.calculus | 14 |
| key.core.infflow | 11 |
| key.ncore.matcher | 6 |
| key.core.testgen | 3 |
| key.util | 3 |
| keyext.isabelletranslation | 3 |

## Details (grouped by category, module, file)

### deprecation (815)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/loader/JP2KeYConverter.java` — 51
  * `key.core/src/main/java/de/uka/ilkd/key/logic/TermBuilder.java` — 34
  * `key.core/src/main/java/de/uka/ilkd/key/java/KeYJavaASTFactory.java` — 24
  * `key.core/src/main/java/de/uka/ilkd/key/logic/BoundVariableTools.java` — 20
  * `key.core/src/main/java/de/uka/ilkd/key/logic/label/TermLabelManager.java` — 20
  * `key.core/src/main/java/de/uka/ilkd/key/proof/TermTacletAppIndex.java` — 19
  * `key.core/src/main/java/de/uka/ilkd/key/pp/PrettyPrinter.java` — 17
  * `key.core/src/main/java/de/uka/ilkd/key/logic/TermImpl.java` — 14
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/JFunction.java` — 13
  * `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/WhileInvariantTransformer.java` — 13
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/AssumesInstantiator.java` — 13
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/LocalVariableDeclaration.java` — 12
  * `key.core/src/main/java/de/uka/ilkd/key/rule/SyntacticalReplaceVisitor.java` — 11
  * `key.core/src/main/java/de/uka/ilkd/key/smt/AbstractSMTTranslator.java` — 11
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/CompilationUnit.java` — 10
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ProgramSV.java` — 10
  * `key.core/src/main/java/de/uka/ilkd/key/nparser/builder/ExpressionBuilder.java` — 10
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/reference/MethodReference.java` — 9
* **key.ncore**
  * `key.ncore/src/main/java/org/key_project/logic/op/AbstractSortedOperator.java` — 9
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/FieldDeclaration.java` — 8
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/reference/ArrayReference.java` — 8
  * `key.core/src/main/java/de/uka/ilkd/key/logic/LabeledTermImpl.java` — 8
  * `key.core/src/main/java/de/uka/ilkd/key/rule/conditions/StaticMethodCondition.java` — 8
  * `key.core/src/main/java/de/uka/ilkd/key/java/JavaInfo.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/JavaDeclaration.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/MethodDeclaration.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/TypeDeclaration.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/reference/SpecialConstructorReference.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Exec.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Try.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/nparser/builder/FunctionPredicateBuilder.java` — 7
  * `key.core/src/main/java/de/uka/ilkd/key/rule/QueryExpand.java` — 7
* **key.ncore.calculus**
  * `key.ncore.calculus/src/main/java/org/key_project/prover/rules/instantiation/caches/AssumesFormulaInstantiationCache.java` — 7
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/InheritanceSpecification.java` — 6
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/ParameterDeclaration.java` — 6
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/MethodBodyStatement.java` — 6
  * `key.core/src/main/java/de/uka/ilkd/key/logic/label/OriginTermLabel.java` — 6
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ParametricFunctionDecl.java` — 6
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/IfInstantiationCachePool.java` — 6
* **key.ncore**
  * `key.ncore/src/main/java/org/key_project/logic/op/AbstractOperator.java` — 6
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/ArrayInitializer.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Case.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Default.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/LoopInit.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Switch.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/java/loader/CreateArrayMethodBuilder.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/logic/equality/ProofIrrelevancyProperty.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/pp/LogicPrinter.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/rule/conditions/MayExpandMethodCondition.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/rule/inst/SVInstantiations.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/rule/match/vm/JavaListSVMatcher.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/VariableDeclaration.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/For.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/ForUpdates.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/LoopStatement.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/java/visitor/ProgramReplaceVisitor.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/logic/JTerm.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ObserverFunction.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ProgramMethod.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/proof/OpReplacer.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/rule/AuxiliaryContractBuilders.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/rule/LightweightSyntacticalReplaceVisitor.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/rule/LoopInvariantBuiltInRuleApp.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/rule/conditions/TermLabelCondition.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/MethodCall.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/smt/newsmt2/QuantifierHandler.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/PositionedLabeledString.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/PositionedString.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/jml/translation/JMLSpecFactory.java` — 4
* **key.core.infflow**
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/proof/init/StateVars.java` — 4
* **key.ncore.calculus**
  * `key.ncore.calculus/src/main/java/org/key_project/prover/rules/instantiation/AssumesFormulaInstSeq.java` — 4
* **key.ncore.matcher**
  * `key.ncore.matcher/src/main/java/org/key_project/prover/rules/matcher/compiler/OperatorPlan.java` — 4
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/KeYProgModelInfo.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/InterfaceDeclaration.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/LabeledStatement.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/JOperatorSV.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ParametricFunctionInstance.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/Transformer.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/macros/FinishSymbolicExecutionUntilMergePointMacro.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/proof/ProgVarReplacer.java` — 3
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
* **key.ncore**
  * `key.ncore/src/main/java/org/key_project/logic/Term.java` — 3
* **key.ncore.calculus**
  * `key.ncore.calculus/src/main/java/org/key_project/prover/rules/instantiation/ListInstantiation.java` — 3
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/control/instantiation_model/TacletInstantiationModel.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/AnnotationInterfaceDeclaration.java` — 2
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
  * `key.core/src/main/java/de/uka/ilkd/key/settings/ProofSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/StrategyPresetsSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/StrategySettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/settings/TermLabelSettings.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/smt/SMTObjTranslator.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/AuxiliaryContract.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/speclang/ContractFactory.java` — 2
* **key.core.infflow**
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/ProofObligationVars.java` — 2
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/po/snippet/BasicBlockExecutionSnippet.java` — 2
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/po/snippet/BasicSymbolicExecutionSnippet.java` — 2
* **key.core.testgen**
  * `key.core.testgen/src/main/java/de/uka/ilkd/key/testgen/TestGenerationSettings.java` — 2
* **key.ncore**
  * `key.ncore/src/main/java/org/key_project/logic/TermCreationException.java` — 2
  * `key.ncore/src/main/java/org/key_project/logic/op/Function.java` — 2
* **key.ncore.matcher**
  * `key.ncore.matcher/src/main/java/org/key_project/prover/rules/matcher/compiler/BinderMatcher.java` — 2
* **keyext.isabelletranslation**
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/IsabelleTranslationSettings.java` — 2
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/TypeConverter.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/ccatch/CcatchReturnValParameterDeclaration.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/AnnotationInterfaceMemberDeclaration.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/Extends.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/Implements.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/BinaryAssignment.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/ParenthesizedExpression.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/UnaryAssignment.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/BinaryOperator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/Conditional.java` — 1
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
  * `key.core/src/main/java/de/uka/ilkd/key/java/visitor/CreatingASTVisitor.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/visitor/ProgVarReplaceVisitor.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/visitor/UndeclaredProgramVariableCollector.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/MethodStackInfo.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/equality/IrrelevantTermLabelsProperty.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/label/LabelCollection.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/PrefixTermTacletAppIndexCache.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/init/AbstractOperationPO.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/LoopScopeInvariantRule.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/ObserverToUpdateRule.java` — 1
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
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/TriggersSet.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/quantifierHeuristics/theory/HeapArrayTheorySupport.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/termgenerator/SuperTermGenerator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/taclettranslation/assumptions/GenericTranslator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/taclettranslation/lemma/DefaultLemmaGenerator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/util/mergerule/MergeRuleUtils.java` — 1
* **key.core.infflow**
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/po/snippet/MethodCallPredicateSnippet.java` — 1
* **key.core.testgen**
  * `key.core.testgen/src/main/java/de/uka/ilkd/key/testgen/oracle/OracleGenerator.java` — 1
* **key.ncore**
  * `key.ncore/src/main/java/org/key_project/logic/op/SortedOperator.java` — 1
* **keyext.isabelletranslation**
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/translation/IsabelleMasterHandler.java` — 1

### other (46)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/strategy/IntegerStrategy.java` — 46

### try (5)

* **key.core**
  * `key.core/src/test/java/de/uka/ilkd/key/proof/TestRuleAppIndexMode.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/prover/impl/ApplyStrategy.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/prover/impl/ParallelProver.java` — 1

### unchecked (3)

* **key.util**
  * `key.util/src/main/java/org/key_project/util/collection/ImmutableArray.java` — 3

### cast (1)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AnnotationMover.java` — 1

