# KeY compiler warning inventory

* generated: 2026-10-24T23:11:10.003883+00:00
* command: `./gradlew --console=plain testClasses --offline --rerun-tasks`

Total warnings: **606** across **15** modules, in **7** categories.

## Summary by category

| category | count |
|---|---|
| deprecation | 240 |
| serial | 189 |
| this-escape | 83 |
| unchecked | 64 |
| rawtypes | 25 |
| cast | 3 |
| overrides | 2 |

## Summary by module

| module | count |
|---|---|
| key.core | 214 |
| key.ui | 101 |
| key.util | 65 |
| keyext.caching | 35 |
| keyext.isabelletranslation | 32 |
| key.ncore | 31 |
| keyext.slicing | 27 |
| keyext.exploration | 26 |
| key.core.infflow | 24 |
| key.ncore.calculus | 23 |
| keyext.ui.testgen | 7 |
| key.ncore.matcher | 6 |
| keyext.proofmanagement | 6 |
| key.core.wd | 5 |
| key.core.testgen | 4 |

## Details (grouped by category, module, file)

### deprecation (240)

* **key.core**
  * `key.core/src/test/java/de/uka/ilkd/key/logic/equality/TestEqualsModProperty.java` — 30
  * `key.core/src/main/java/de/uka/ilkd/key/logic/TermBuilder.java` — 27
  * `key.core/src/main/java/de/uka/ilkd/key/logic/label/TermLabelManager.java` — 20
  * `key.core/src/test/java/de/uka/ilkd/key/logic/TestTermFactory.java` — 17
  * `key.core/src/test/java/de/uka/ilkd/key/logic/TestTermLabelManager.java` — 12
* **key.util**
  * `key.util/src/test/java/org/key_project/util/StringsTest.java` — 12
* **key.ncore**
  * `key.ncore/src/main/java/org/key_project/logic/op/AbstractSortedOperator.java` — 9
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/JavaInfo.java` — 7
* **key.util**
  * `key.util/src/test/java/org/key_project/util/testcase/java/IOUtilTest.java` — 7
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/logic/label/OriginTermLabel.java` — 6
* **key.ncore**
  * `key.ncore/src/main/java/org/key_project/logic/op/AbstractOperator.java` — 6
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/logic/equality/IrrelevantTermLabelsProperty.java` — 5
  * `key.core/src/main/java/de/uka/ilkd/key/rule/inst/SVInstantiations.java` — 5
* **key.ncore.calculus**
  * `key.ncore.calculus/src/main/java/org/key_project/prover/rules/instantiation/caches/AssumesFormulaInstantiationCache.java` — 5
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/logic/JTerm.java` — 4
* **key.core.infflow**
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/proof/init/StateVars.java` — 4
* **key.ncore.calculus**
  * `key.ncore.calculus/src/main/java/org/key_project/prover/rules/instantiation/AssumesFormulaInstSeq.java` — 4
* **key.ncore.matcher**
  * `key.ncore.matcher/src/main/java/org/key_project/prover/rules/matcher/compiler/OperatorPlan.java` — 4
* **key.core**
  * `key.core/src/test/java/de/uka/ilkd/key/logic/LabeledTermImplTest.java` — 3
* **key.ncore**
  * `key.ncore/src/main/java/org/key_project/logic/Term.java` — 3
* **key.ncore.calculus**
  * `key.ncore.calculus/src/main/java/org/key_project/prover/rules/instantiation/ListInstantiation.java` — 3
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/SequentView.java` — 3
* **key.core**
  * `key.core/src/test/java/de/uka/ilkd/key/logic/TestTerm.java` — 2
  * `key.core/src/test/java/de/uka/ilkd/key/logic/sort/TestParametricSorts.java` — 2
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
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/prooftree/ProofTreeView.java` — 2
* **key.util**
  * `key.util/src/main/java/org/key_project/util/EqualsModProofIrrelevancyUtil.java` — 2
  * `key.util/src/main/java/org/key_project/util/java/IOUtil.java` — 2
* **keyext.isabelletranslation**
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/IsabelleTranslationSettings.java` — 2
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/TypeConverter.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/java/transformations/ConstantExpressionEvaluator.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/proof/PrefixTermTacletAppIndexCache.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/java/RecoderExample.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/logic/label/LabelCollectionTest.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/parser/TestParser.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/parser/TestTermParser.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/parser/messages/ParserMessageTest.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/proof/TestGoal.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/proof/io/ProofSaverTest.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/rule/match/vm/ParametricFunctionInterningTest.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/util/ParserExceptionTest.java` — 1
* **key.core.infflow**
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/po/snippet/MethodCallPredicateSnippet.java` — 1
* **key.core.testgen**
  * `key.core.testgen/src/main/java/de/uka/ilkd/key/testgen/oracle/OracleGenerator.java` — 1
* **key.ncore**
  * `key.ncore/src/main/java/org/key_project/logic/op/SortedOperator.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/MainWindow.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/ui/MediatorProofControl.java` — 1
* **keyext.isabelletranslation**
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/translation/IsabelleMasterHandler.java` — 1

### serial (189)

* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/MainWindow.java` — 18
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/SequentView.java` — 12
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/GoalList.java` — 11
* **keyext.slicing**
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/SliceToFixedPointDialog.java` — 7
* **keyext.exploration**
  * `keyext.exploration/src/main/java/org/key_project/exploration/ui/ExplorationStepsList.java` — 6
* **key.core**
  * `key.core/src/testFixtures/java/de/uka/ilkd/key/proof/runallproofs/proofcollection/ForkedTestFileRunner.java` — 5
* **keyext.isabelletranslation**
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/gui/IsabelleProgressDialog.java` — 5
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/gui/IsabelleProofApplyUserAction.java` — 5
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/useractions/ProofMacroUserAction.java` — 4
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/useractions/SMTProofApplyUserAction.java` — 4
* **keyext.caching**
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/actions/CloseAllByReference.java` — 4
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/actions/CloseByReference.java` — 4
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/actions/CopyReferencedProof.java` — 4
* **key.ncore**
  * `key.ncore/src/main/java/org/key_project/util/parsing/RecognitionException.java` — 3
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/useractions/ProofModifyingUserAction.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/useractions/UserAction.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/CurrentGoalView.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/prooftree/ProofTreeView.java` — 3
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/ProgressDialog.java` — 3
* **keyext.caching**
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/ReferenceSearchTable.java` — 3
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/actions/GotoReferenceAction.java` — 3
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/actions/RemoveCachingInformationAction.java` — 3
* **key.core**
  * `key.core/src/testFixtures/java/de/uka/ilkd/key/proof/runallproofs/RunAllProofsTestUnit.java` — 2
* **key.ncore**
  * `key.ncore/src/main/java/org/key_project/util/parsing/LocatableException.java` — 2
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/SearchBar.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/useractions/FocussedAutoModeUserAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/useractions/ProofLoadUserAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/useractions/RunStrategyOnNodeUserAction.java` — 2
* **key.util**
  * `key.util/src/main/java/org/key_project/util/collection/ImmutableArray.java` — 2
  * `key.util/src/main/java/org/key_project/util/collection/ImmutableListArray.java` — 2
  * `key.util/src/main/java/org/key_project/util/collection/ImmutableListList.java` — 2
  * `key.util/src/main/java/org/key_project/util/collection/ImmutableSLList.java` — 2
  * `key.util/src/main/java/org/key_project/util/collection/NotUniqueException.java` — 2
* **keyext.caching**
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/ReferenceSearchButton.java` — 2
* **keyext.exploration**
  * `keyext.exploration/src/main/java/org/key_project/exploration/actions/DeleteFormulaAction.java` — 2
* **keyext.isabelletranslation**
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/IsabelleSettingsProvider.java` — 2
* **keyext.proofmanagement**
  * `keyext.proofmanagement/src/main/java/org/key_project/proofmanagement/CheckConfigDialog.java` — 2
* **keyext.ui.testgen**
  * `keyext.ui.testgen/src/main/java/de/uka/ilkd/key/gui/testgen/TGInfoDialog.java` — 2
* **key.core**
  * `key.core/src/test/java/de/uka/ilkd/key/rule/merge/MergeRuleTests.java` — 1
  * `key.core/src/testFixtures/java/de/uka/ilkd/key/proof/runallproofs/performance/DataRecordingTestFile.java` — 1
  * `key.core/src/testFixtures/java/de/uka/ilkd/key/proof/runallproofs/proofcollection/GroupedProofCollectionUnit.java` — 1
  * `key.core/src/testFixtures/java/de/uka/ilkd/key/proof/runallproofs/proofcollection/ProofCollectionSettings.java` — 1
  * `key.core/src/testFixtures/java/de/uka/ilkd/key/proof/runallproofs/proofcollection/SingletonProofCollectionUnit.java` — 1
  * `key.core/src/testFixtures/java/de/uka/ilkd/key/proof/runallproofs/proofcollection/StatisticsFile.java` — 1
* **key.ncore**
  * `key.ncore/src/main/java/org/key_project/logic/TermCreationException.java` — 1
* **key.ncore.calculus**
  * `key.ncore.calculus/src/main/java/org/key_project/prover/rules/RuleAbortException.java` — 1
  * `key.ncore.calculus/src/main/java/org/key_project/prover/rules/instantiation/IllegalInstantiationException.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/useractions/AutoModeUserAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/useractions/ProofRuleUserAction.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/SequentViewSearchBar.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/InformationWindow.java` — 1
  * `key.ui/src/test/java/de/uka/ilkd/key/gui/tacletmatch/AssumesInputTest.java` — 1
* **key.util**
  * `key.util/src/main/java/org/key_project/util/StripedLruCache.java` — 1
  * `key.util/src/main/java/org/key_project/util/collection/ImmutableLeftistHeap.java` — 1
  * `key.util/src/main/java/org/key_project/util/collection/ImmutableListConcat.java` — 1
  * `key.util/src/main/java/org/key_project/util/collection/ImmutableListReverse.java` — 1
  * `key.util/src/main/java/org/key_project/util/collection/ImmutableListSubList.java` — 1
* **keyext.caching**
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/CachingException.java` — 1
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/ReferenceSearchDialog.java` — 1
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/settings/CachingSettingsProvider.java` — 1
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/toolbar/CachingToggleAction.java` — 1
* **keyext.exploration**
  * `keyext.exploration/src/main/java/org/key_project/exploration/actions/AddFormulaToAntecedentAction.java` — 1
  * `keyext.exploration/src/main/java/org/key_project/exploration/actions/AddFormulaToSuccedentAction.java` — 1
  * `keyext.exploration/src/main/java/org/key_project/exploration/actions/EditFormulaAction.java` — 1
  * `keyext.exploration/src/main/java/org/key_project/exploration/actions/ShowInteractiveBranchesAction.java` — 1
  * `keyext.exploration/src/main/java/org/key_project/exploration/actions/ToggleExplorationAction.java` — 1
* **keyext.isabelletranslation**
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/automation/IsabelleNotFoundException.java` — 1
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/gui/InformationWindow.java` — 1
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/gui/controller/IsabelleTranslateAllAction.java` — 1
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/gui/controller/IsabelleTranslationAction.java` — 1
* **keyext.proofmanagement**
  * `keyext.proofmanagement/src/main/java/org/key_project/proofmanagement/ProofManagementExt.java` — 1
  * `keyext.proofmanagement/src/main/java/org/key_project/proofmanagement/check/ProofManagementException.java` — 1
* **keyext.slicing**
  * `keyext.slicing/src/main/java/org/key_project/slicing/SlicingSettingsProvider.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/HtmlDialog.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/PanZoomImageView.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/PreviewDialog.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/RuleStatisticsDialog.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/SlicingLeftPanel.java` — 1
* **keyext.ui.testgen**
  * `keyext.ui.testgen/src/main/java/de/uka/ilkd/key/gui/testgen/TestgenOptionsPanel.java` — 1

### this-escape (83)

* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/proof/Proof.java` — 11
  * `key.core/src/main/java/de/uka/ilkd/key/java/Services.java` — 3
* **keyext.caching**
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/settings/ProofCachingSettings.java` — 3
* **keyext.slicing**
  * `keyext.slicing/src/main/java/org/key_project/slicing/SlicingSettings.java` — 3
* **key.core.infflow**
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/po/IFProofObligationVars.java` — 2
* **key.ncore.calculus**
  * `key.ncore.calculus/src/main/java/org/key_project/prover/rules/Taclet.java` — 2
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/MainWindowAction.java` — 2
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/colors/ColorSettings.java` — 2
* **keyext.exploration**
  * `keyext.exploration/src/main/java/org/key_project/exploration/ui/ExplorationStepsList.java` — 2
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/logic/sort/ProgramSVSort.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/parser/AbstractTestTermParser.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/parser/TestIntLiteralParsing.java` — 1
  * `key.core/src/testFixtures/java/de/uka/ilkd/key/proof/runallproofs/proofcollection/TestFile.java` — 1
* **key.core.testgen**
  * `key.core.testgen/src/main/java/de/uka/ilkd/key/testgen/TestCaseGenerator.java` — 1
* **key.core.wd**
  * `key.core.wd/src/main/java/de/uka/ilkd/key/wd/BlockWellDefinedness.java` — 1
  * `key.core.wd/src/main/java/de/uka/ilkd/key/wd/LoopWellDefinedness.java` — 1
  * `key.core.wd/src/main/java/de/uka/ilkd/key/wd/WdProfile.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/core/KeYMediator.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/GoalList.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/SearchBar.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/actions/AutoSave.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/keyshortcuts/KeyStrokeSettings.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/SequentView.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/InformationWindow.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/smt/ProgressDialog.java` — 1
  * `key.ui/src/main/java/de/uka/ilkd/key/ui/AbstractMediatorUserInterfaceControl.java` — 1
* **key.util**
  * `key.util/src/main/java/org/key_project/util/bean/Bean.java` — 1
  * `key.util/src/main/java/org/key_project/util/lookup/Lookup.java` — 1
  * `key.util/src/main/java/org/key_project/util/lookup/PLookup.java` — 1
* **keyext.caching**
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/ReferenceSearchButton.java` — 1
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/ReferenceSearchDialog.java` — 1
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/actions/CloseAllByReference.java` — 1
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/settings/CachingSettingsProvider.java` — 1
  * `keyext.caching/src/main/java/de/uka/ilkd/key/gui/plugins/caching/toolbar/CachingToggleAction.java` — 1
* **keyext.exploration**
  * `keyext.exploration/src/main/java/org/key_project/exploration/ExplorationModeModel.java` — 1
  * `keyext.exploration/src/main/java/org/key_project/exploration/actions/AddFormulaToAntecedentAction.java` — 1
  * `keyext.exploration/src/main/java/org/key_project/exploration/actions/AddFormulaToSuccedentAction.java` — 1
  * `keyext.exploration/src/main/java/org/key_project/exploration/actions/DeleteFormulaAction.java` — 1
  * `keyext.exploration/src/main/java/org/key_project/exploration/actions/EditFormulaAction.java` — 1
  * `keyext.exploration/src/main/java/org/key_project/exploration/actions/ShowInteractiveBranchesAction.java` — 1
  * `keyext.exploration/src/main/java/org/key_project/exploration/actions/ToggleExplorationAction.java` — 1
* **keyext.isabelletranslation**
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/IsabelleSettingsProvider.java` — 1
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/gui/InformationWindow.java` — 1
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/gui/IsabelleProgressDialog.java` — 1
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/gui/controller/IsabelleTranslateAllAction.java` — 1
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/gui/controller/IsabelleTranslationAction.java` — 1
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/translation/IsabelleMasterHandler.java` — 1
* **keyext.slicing**
  * `keyext.slicing/src/main/java/org/key_project/slicing/DependencyTracker.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/SlicingSettingsProvider.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/HtmlDialog.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/PanZoomImageView.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/PreviewDialog.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/RuleStatisticsDialog.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/ShowCreatedByAction.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/ShowGraphAction.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/ShowNodeInfoAction.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/SliceToFixedPointDialog.java` — 1
  * `keyext.slicing/src/main/java/org/key_project/slicing/ui/SlicingLeftPanel.java` — 1
* **keyext.ui.testgen**
  * `keyext.ui.testgen/src/main/java/de/uka/ilkd/key/gui/testgen/CounterExampleAction.java` — 1
  * `keyext.ui.testgen/src/main/java/de/uka/ilkd/key/gui/testgen/TGInfoDialog.java` — 1
  * `keyext.ui.testgen/src/main/java/de/uka/ilkd/key/gui/testgen/TestGenerationAction.java` — 1
  * `keyext.ui.testgen/src/main/java/de/uka/ilkd/key/gui/testgen/TestgenOptionsPanel.java` — 1

### unchecked (64)

* **key.core**
  * `key.core/src/test/java/de/uka/ilkd/key/rule/TestApplyTaclet.java` — 16
* **key.util**
  * `key.util/src/test/java/org/key_project/util/collection/ImmutableListConcatTest.java` — 4
* **key.core**
  * `key.core/src/test/java/de/uka/ilkd/key/logic/TestTermLabelManager.java` — 3
* **key.util**
  * `key.util/src/main/java/org/key_project/util/collection/ImmutableArray.java` — 3
* **keyext.exploration**
  * `keyext.exploration/src/main/java/org/key_project/exploration/ExplorationExtension.java` — 3
* **keyext.isabelletranslation**
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/IsabelleTranslationExtension.java` — 3
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/rule/inst/SVInstantiations.java` — 2
  * `key.core/src/test/java/de/uka/ilkd/key/rule/TacletForTests.java` — 2
* **key.core.infflow**
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/JavaInfFlowProfile.java` — 2
* **key.core.wd**
  * `key.core.wd/src/main/java/de/uka/ilkd/key/wd/WdProfile.java` — 2
* **key.ncore.calculus**
  * `key.ncore.calculus/src/main/java/org/key_project/prover/strategy/costbased/feature/SortComparisonFeature.java` — 2
* **key.util**
  * `key.util/src/main/java/org/key_project/util/collection/DirectedGraph.java` — 2
* **keyext.isabelletranslation**
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/automation/IsabelleRule.java` — 2
* **keyext.proofmanagement**
  * `keyext.proofmanagement/src/main/java/org/key_project/proofmanagement/io/HTMLReport.java` — 2
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/java/ast/SourceElement.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/equality/EqualsModProperty.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/equality/IrrelevantTermLabelsProperty.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/equality/RenamingSourceElementProperty.java` — 1
  * `key.core/src/main/java/de/uka/ilkd/key/logic/equality/RenamingTermProperty.java` — 1
* **key.core.infflow**
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/rule/InfFlowContractAppTaclet.java` — 1
* **key.ncore**
  * `key.ncore/src/main/java/org/key_project/logic/Property.java` — 1
  * `key.ncore/src/main/java/org/key_project/logic/op/Modality.java` — 1
* **key.ncore.calculus**
  * `key.ncore.calculus/src/main/java/org/key_project/prover/engine/SingleRuleApplicationInfo.java` — 1
  * `key.ncore.calculus/src/main/java/org/key_project/prover/strategy/costbased/feature/LetFeature.java` — 1
  * `key.ncore.calculus/src/main/java/org/key_project/prover/strategy/costbased/termfeature/ApplyTFFeature.java` — 1
* **key.util**
  * `key.util/src/main/java/org/key_project/util/EqualsAndHashCodeDelegator.java` — 1
  * `key.util/src/main/java/org/key_project/util/collection/ImmutableSet.java` — 1
  * `key.util/src/main/java/org/key_project/util/collection/WeakValueLinkedHashMap.java` — 1
  * `key.util/src/main/java/org/key_project/util/java/ArrayUtil.java` — 1
* **keyext.isabelletranslation**
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/translation/IsabelleHandlerServices.java` — 1

### rawtypes (25)

* **key.core.infflow**
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/po/snippet/BasicSymbolicExecutionSnippet.java` — 3
* **key.util**
  * `key.util/src/test/java/org/key_project/util/testcase/collection/TestSLListOfString.java` — 3
* **key.ncore.calculus**
  * `key.ncore.calculus/src/main/java/org/key_project/prover/rules/instantiation/caches/AssumesFormulaInstantiationCache.java` — 2
* **key.util**
  * `key.util/src/main/java/org/key_project/util/collection/DefaultImmutableMap.java` — 2
  * `key.util/src/test/java/org/key_project/util/testcase/collection/TestSetAsListOfString.java` — 2
* **key.core**
  * `key.core/src/main/java/de/uka/ilkd/key/logic/VariableNamer.java` — 1
  * `key.core/src/test/java/de/uka/ilkd/key/parser/TestTacletParser.java` — 1
  * `key.core/src/testFixtures/java/de/uka/ilkd/key/proof/runallproofs/proofcollection/StatisticsFile.java` — 1
* **key.core.infflow**
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/macros/FinishAuxiliaryBlockComputationMacro.java` — 1
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/macros/StartAuxiliaryBlockComputationMacro.java` — 1
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/macros/UseInformationFlowContractMacro.java` — 1
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/po/snippet/BasicLoopExecutionSnippet.java` — 1
  * `key.core.infflow/src/main/java/de/uka/ilkd/key/informationflow/rule/InfFlowWhileInvariantRule.java` — 1
* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/MainWindow.java` — 1
* **key.util**
  * `key.util/src/main/java/org/key_project/util/StripedLruCache.java` — 1
  * `key.util/src/test/java/org/key_project/util/collection/ImmutableListConcatTest.java` — 1
* **keyext.exploration**
  * `keyext.exploration/src/main/java/org/key_project/exploration/ExplorationExtension.java` — 1
* **keyext.isabelletranslation**
  * `keyext.isabelletranslation/src/main/java/org/key_project/isabelletranslation/IsabelleTranslationExtension.java` — 1

### cast (3)

* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/SequentView.java` — 2
* **key.util**
  * `key.util/src/main/java/org/key_project/util/java/ArrayUtil.java` — 1

### overrides (2)

* **key.ui**
  * `key.ui/src/main/java/de/uka/ilkd/key/gui/nodeviews/SequentView.java` — 1
* **key.util**
  * `key.util/src/main/java/org/key_project/util/collection/WeakValueLinkedHashMap.java` — 1

