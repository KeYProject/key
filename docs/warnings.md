# KeY compiler warning inventory

* generated: 2026-10-24T22:32:33.077547+00:00
* command: `./gradlew --console=plain testClasses --offline --rerun-tasks`

Total warnings: **224** across **2** modules, in **8** categories.

## Summary by category

| category | count |
|---|---|
| deprecation | 87 |
| serial | 61 |
| this-escape | 44 |
| unchecked | 16 |
| try | 10 |
| rawtypes | 4 |
| cast | 1 |
| dangling-doc-comments | 1 |

## Summary by module

| module | count |
|---|---|
| key.core | 124 |
| key.ui | 100 |

## Details (grouped by category, module, file)

### deprecation (87)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/logic/TermFactory.java` — 20
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/StatementBlock.java` — 13
  * `key.core/src/main/java/de/uka/ilkd/key/logic/ClashFreeSubst.java` — 12
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/JAbstractSortedOperator.java` — 9
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/Operator.java` — 8
  * `key.core/src/main/java/de/uka/ilkd/key/rule/TacletApp.java` — 3
  * `key.core/src/test/java/de/uka/ilkd/key/strategy/quantifierHeuristics/TestTriggersSet.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/declaration/Throws.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/IProgramMethod.java` — 2
  * `key.core/src/test/java/de/uka/ilkd/key/util/TestLinkedHashMapWrapper.java` — 2
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/WindowUserInterfaceControl.java` — 2
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/JavaService.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/ContextStatementBlock.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/Declaration.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/JavaNonTerminalProgramElement.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/operator/DLEmbeddedExpression.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/ProgramPrefix.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/IObserverFunction.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/OneStepSimplifier.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/scripts/ProofScriptParserTest.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/strategy/TieBreakComparatorPropertyTest.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ProofManagementAction.java` — 1

### serial (61)

* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/InfoView.java` — 7
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/TaskTree.java` — 6
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/SourceView.java` — 6
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/TermLabelMenu.java` — 4
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/SourceHighlightDocument.java` — 4
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/StrategySelectionView.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/JavaDocument.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/RecentFileMenu.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/AutoModeAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SelectionBackAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SelectionForwardAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ShowActiveSettingsAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToggleSourceViewTooltipAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/DropdownSelectionButton.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/MainStatusLine.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/MaxRuleAppSlider.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ExitMainAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/HidePackagePrefixToggleAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/OpenFileAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/OpenSingleJavaFileAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToggleProofTreeTooltipAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToggleSequentViewTooltipAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/UnicodeToggleAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/EmptySequent.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/prooftree/GUIProofTreeModel.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/SourceViewFrame.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/proof/mgt/BasicTask.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/proof/mgt/TaskTreeModel.java` — 1

### this-escape (44)

* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/utilities/LexerHighlighter.java` — 8
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/StatementBlock.java` — 3
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/abstraction/KeYJavaType.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/literal/LongLiteral.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/logic/op/ProgramVariable.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/Node.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/Statistics.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/InfoView.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/MaxRuleAppSlider.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/SelectionHistory.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/TaskTree.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/AboutAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/AutoModeAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ExitMainAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/LemmaGenerationAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/LemmaGenerationBatchModeAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/OpenFileAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/OpenSingleJavaFileAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/QuickLoadAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SelectionBackAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/SelectionForwardAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ShowActiveSettingsAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/TermLabelMenu.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToggleProofTreeTooltipAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToggleSequentViewTooltipAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/ToggleSourceViewTooltipAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/UnicodeToggleAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/EmptySequent.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/notification/NotificationManager.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/DropdownSelectionButton.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/JavaDocument.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/SourceHighlightDocument.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/sourceview/SourceViewFrame.java` — 1

### unchecked (16)

* **key.core**
  * `key.core/src/test/java/de/uka/ilkd/key/rule/TestSchemaModalOperators.java` — 6
  * `key.core/src/main/java/de/uka/ilkd/key/rule/OneStepSimplifierRuleApp.java` — 4
  * `key.core/src/main/java/de/uka/ilkd/key/rule/Taclet.java` — 2
  * `key.core/src/main/java/de/uka/ilkd/key/ldt/AbstractLDT.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/BuiltInRule.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/OneStepSimplifier.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/WindowUserInterfaceControl.java` — 1

### try (10)

* **key.core**
  * `key.core/src/test/java/de/uka/ilkd/key/prover/mt/ListenerSuspensionTest.java` — 6
  * `key.core/src/test/java/de/uka/ilkd/key/prover/mt/MergeRuleMultiThreadGuardTest.java` — 4

### rawtypes (4)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/logic/ClashFreeSubst.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/OneStepSimplifier.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/OneStepSimplifierRuleApp.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/rule/Taclet.java` — 1

### cast (1)

* **key.core**
  * `key.core/src/test/java/de/uka/ilkd/key/strategy/QueueRuleApplicationManagerParkingLocalityTest.java` — 1

### dangling-doc-comments (1)

* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/WindowUserInterfaceControl.java` — 1

