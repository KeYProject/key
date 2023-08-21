/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs;


import java.io.IOException;
import java.util.Date;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ForkMode;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionSettings;

import org.key_project.util.java.IOUtil;

import org.junit.jupiter.api.Assertions;

/**
 * @author Alexander Weigl
 * @version 1 (08.02.23)
 */
public class ProofCollections {
    public static ProofCollection automaticJavaDL() throws IOException {
        var settings = new ProofCollectionSettings(new Date());
        /*
         * Defines a base directory.
         * All paths in this file are treated relative to base directory (except path for base
         * directory itself).
         */
        settings.setBaseDirectory("../key.ui/examples/");

        /*
         * Defines a statistics file.
         * Path is relative to base directory.
         */
        settings.setStatisticsFile("build/reports/runallproofs/runStatistics.csv");

        /*
         * Fork mode setting, can be declared to create subprocesses while running tests declared in
         * this file.
         * Possible modes: noFork-all files are proven within a single process
         * pervar g = c.group("- one subprocess is created for each group
         * perFile-one subprocess is created for each file
         */
        settings.setForkMode(ForkMode.PERGROUP);

        /*
         * Enable or disable proof reloading.
         * If enabled, closed proofs will be saved and reloaded after prover is finished.
         */
        settings.setReloadEnabled(true);

        /*
         * Temporary directory, which is used for inter process communication when using forked
         * mode.
         * The given path is relative to baseDirectory.
         */
        settings.setTempDir("build/runallproofs_tmp");

        /*
         * If the fork mode is not set to noFork, the launched subprocesses are terminated as
         * soon as the timeout specified here has elapsed. No timeout occurs if not specified.
         *
         * Timeout per subprocess in seconds
         */
        settings.setForkTimeout(2000);

        /*
         * If the fork mode is not set to noFork, the launched subprocesses
         * get the specified amount of heap memory.
         *
         * Heap memory for subprocesses (like 500m or 2G)
         */
        // forkMemory = 1000m

        /*
         * To run the forked JVM in debug mode, set the TCP port to listen to here.
         * You can prefix the port with "wait:" to make the JVM suspend till the
         * process has connected.
         *
         * Examples: forkDebugPort = "8000"
         * forkDebugPort = "wait:1234"
         */
        // forkDebugPort = "wait:1234"

        /*
         * By default, runAllProofs does not print a lot of information.
         * Set this to true to get more output.
         */
        settings.setVerboseOutput(true);
        // verboseOutput = true

        /*
         * By default, runAllProofs runs all groups in this file.
         * By naming a comma separated list of groups here, the
         * test can be restricted to these groups (for debugging).
         */
        // runOnlyOn = group1,group2

        settings.setKeySettings(loadFromFile("automaticJAVADL.properties"));

        var c = new ProofCollection(settings);

        // Examples used in the new book
        var newBook = c.group("newBook");
        newBook.provable("newBook/09.list_modelfield/ArrayList.add.key");
        newBook.provable("newBook/09.list_modelfield/ArrayList.remFirst.key");
        newBook.provable("newBook/09.list_modelfield/ArrayList.empty.key");
        newBook.provable("newBook/09.list_modelfield/ArrayList.size.key");
        newBook.provable("newBook/09.list_modelfield/ArrayList.get.key");

        var oldBook = c.group("oldBook");
        oldBook.provable("standard_key/BookExamples/02FirstOrderLogic/Ex2.58.key");
        oldBook.provable("standard_key/BookExamples/03DynamicLogic/Sect3.3.1.key");;


        // Comprehension Tests
        var comprehensions = c.group("comprehensions");
        comprehensions.provable("heap/comprehensions/general_sum.key");
        comprehensions.provable("heap/comprehensions/sum0.key");
        comprehensions.provable("heap/comprehensions/sum1.key");
        comprehensions.provable("heap/comprehensions/sum2.key");
        comprehensions.provable("heap/comprehensions/sum3.key");
        comprehensions.provable("heap/comprehensions/segsum.key");
        comprehensions.provable("heap/comprehensions/bsum_negative.key");
        comprehensions.provable("heap/comprehensions/bsum_neg2.key");
        comprehensions.provable("heap/comprehensions/bsumSplit.key");
        comprehensions.provable("heap/comprehensions/bprodSplit.key");
        comprehensions.notprovable("heap/comprehensions/bsumSplitInvalid.key");


        // Performance tests
        var performance = c.group("performance");
        performance.provable(
            "performance-test/Disjoint(Disjoint__disjoint_08()).JML_operation_contract.0.key");
        performance.provable(
            "performance-test/Disjoint(Disjoint__disjoint2_08()).JML_operation_contract.0.key");
        performance.provable(
            "performance-test/AccessChain1(AccessChain1__foo_08()).JML_operation_contract.0.key");
        performance.provable(
            "performance-test/AccessChain4(AccessChain4__foo_08()).JML_operation_contract.0.key");
        performance.provable(
            "performance-test/Disjoint(Disjoint__xZero_08()).JML_operation_contract.0.key");
        performance.provable(
            "performance-test/Dynamic(Dynamic__foo_08()).JML_operation_contract.0.key");
        performance.provable(
            "performance-test/DynamicGhost(DynamicGhost__dynamicGhost_08()).JML_normal_behavior_operation_contract.0.key");
        performance.provable(
            "performance-test/GhostFrame(GhostFrame__foo_08()).JML_operation_contract.0.key");
        performance.provable(
            "performance-test/Modelfield(Modelfield__foo_08()).JML_operation_contract.0.key");

        // Test performance of PO construction
        var performancePOConstruction = c.group("performancePOConstruction");
        performancePOConstruction.provable(
            "performance-test/Test(Test__a0(int)).JML_normal_behavior_operation_contract.0.key");
        performancePOConstruction.provable(
            "performance-test/Test(Test__a1(int)).JML_normal_behavior_operation_contract.0.key");
        performancePOConstruction.provable(
            "performance-test/Test(Test__f1(int)).JML_normal_behavior_operation_contract.0.key");


        // Tests for rule application restrictions
        var g = c.group("applicationRestrictions");
        g.provable("heap/polarity_tests/wellformed1.key");
        g.notprovable("heap/polarity_tests/wellformed2.key");
        g.provable("heap/polarity_tests/wellformed3.key");
        g.notprovable("heap/polarity_tests/wellformed4.key");
        g.provable("heap/polarity_tests/wellformed5.key");
        g.notprovable("heap/polarity_tests/wellformed6.key");
        g.provable("heap/polarity_tests/wellformed7.key");
        g.notprovable("heap/polarity_tests/wellformed8.key");
        g.provable("heap/polarity_tests/wellformed9.key");
        g.notprovable("heap/polarity_tests/wellformed10.key");
        g.notprovable("heap/polarity_tests/wellformed11.key");


        // Tests for block & loop contracts:
        g = c.group("blockContracts");
        g.provable("heap/block_contracts/Simple__add.key");
        g.provable("heap/block_contracts/Simple__addAbsoluteValues.key");
        g.provable("heap/block_contracts/Simple__addWithJump.key");
        g.provable("heap/block_contracts/Simple__addWithTwoBlockContracts.key");
        g.provable("heap/block_contracts/Simple__generateByteArray.key");
        g.provable("heap/block_contracts/Simple__getLength.key");
        g.provable("heap/block_contracts/Simple__square.key");
        g.provable("heap/block_contracts/Simple__unnecessaryBlockContract.key");
        g.provable("heap/block_contracts/Simple__unnecessaryLoopInvariant.key");
        // the following test has a reload problem probably caused by the one -step-simplifier
        // provable: ./heap/block_contracts/GreatestCommonDivisor.key");
        g.provable("standard_key/java_dl/jml-assert/assert.key");
        g.provable("standard_key/java_dl/jml-assert/assert_assume_order.key");
        g.provable("heap/block_loop_contracts/SimpleVariants/sum_onBlock_external.key");
        g.provable("heap/block_loop_contracts/SimpleVariants/sum_onBlock_internal.key");
        g.provable("heap/block_loop_contracts/SimpleVariants/sum_onBlock_loop.key");
        g.provable("heap/block_loop_contracts/SimpleVariants/sum_onLoop_external.key");
        g.provable("heap/block_loop_contracts/SimpleVariants/sum_onLoop_internal.key");
        g.provable("heap/block_loop_contracts/SimpleVariants/sum_onLoop_loop.key");
        g.provable("heap/block_loop_contracts/Free/blockContracts0.key");
        g.provable("heap/block_loop_contracts/Free/blockContracts1.key");
        g.notprovable("heap/block_loop_contracts/Finally/block_finally.key");
        g.notprovable("heap/block_loop_contracts/Finally/loop_finally.key");


        g = c.group("jmlAsserts");
        g.provable("standard_key/java_dl/jml-assert/assert.key");
        g.provable("heap/block_loop_contracts/Free/assertions0.key");
        g.provable("heap/block_loop_contracts/Free/assertions1.key");
        // issue 1669
        g.provable("standard_key/java_dl/jml-assert/recursion-assert.key");
        g.provable("standard_key/java_dl/jml-assert/recursion-assume.key");
        g.provable("standard_key/java_dl/jml-assert/quantor-assert.key");
        g.provable("standard_key/java_dl/jml-assert/quantor-assume.key");
        // issue 1698
        g.provable("standard_key/java_dl/jml-assert/model-methods-static-static.key");
        g.provable("standard_key/java_dl/jml-assert/model-methods-instance-static.key");
        g.provable(
            "standard_key/java_dl/jml-assert/model-methods-instance-instance.key");
        g.provable("standard_key/java_dl/jml-assert/model-methods-static-instance.key");
        // \old()
        g.provable("standard_key/java_dl/jml-assert/assert-old/inc-field.key");
        g.provable("standard_key/java_dl/jml-assert/assert-old/inc-parameter.key");
        g.provable("standard_key/java_dl/jml-assert/assert-old/inc-parameter-field.key");
        g.provable("standard_key/java_dl/jml-assert/assert-old/inc-ghost-field.key");


        // Tests for Java Card (should also include the API, pending fix to bug //1475)
        g = c.group("javaCard");
        g.provable("heap/javacard/updateBalance0.key");
        g.provable("heap/javacard/updateBalance1.key");
        g.provable("heap/javacard/setArray1.key");
        g.provable("heap/javacard/setArray2.key");
        // For this only "half" of the proof is done(see bug //1475), but it makes sure that the PO
        // with two subproofs is
        g.provable("heap/javacard/arrayFillNonAtomic.key");


        // Other tests:
        g.provable("heap/coincidence_count/project.key");
        g.provable("heap/verifyThis11_1_Maximum/project.key");
        g.provable("heap/fm12_01_LRS/lcp.key");
        g.provable("heap/SemanticSlicing/project.key");
        g.provable("heap/information_flow/ArrayList_contains.key");
        g.provable("heap/information_flow/ArrayList_get.key");
        g.provable("heap/information_flow/ArrayList_size.key");
        g.provable("heap/information_flow/UpdateAbstraction_ex7_3_secure.key");
        g.provable("heap/information_flow/UpdateAbstraction_ex7_4_secure.key");
        g.provable("heap/information_flow/UpdateAbstraction_ex7_5_secure.key");
        g.provable("heap/information_flow/UpdateAbstraction_ex7_6_secure.key");
        g.provable("heap/information_flow/UpdateAbstraction_ex9_secure.key");

        g = c.group("list");
        g.provable("heap/list/ArrayList_add.key");
        g.provable("heap/list/ArrayList_ArrayList.key");
        g.provable("heap/list/ArrayList_concatenate.key");
        g.provable("heap/list/ArrayList_contains_dep.key");
        g.provable("heap/list/ArrayList_enlarge.key");
        g.provable("heap/list/ArrayList_footprint.key");
        g.provable("heap/list/ArrayList_get_dep.key");
        g.provable("heap/list/ArrayList_get_exceptional.key");
        g.provable("heap/list/ArrayList_get_normal.key");
        g.provable("heap/list/ArrayList_inv.key");
        g.provable("heap/list/ArrayList_iterator.key");
        g.provable("heap/list/ArrayList_size_dep.key");
        g.provable("heap/list/ArrayList_size.key");
        g.provable("heap/list/ArrayList.ArrayListIterator_ArrayListIterator.key");
        g.provable("heap/list/ArrayList.ArrayListIterator_hasNext_dep.key");
        g.provable("heap/list/ArrayList.ArrayListIterator_hasNext.key");
        g.provable("heap/list/ArrayList.ArrayListIterator_inv.key");
        g.provable("heap/list/ArrayList.ArrayListIterator_list.key");
        g.provable("heap/list/ArrayList.ArrayListIterator_next_exceptional.key");
        g.provable("heap/list/ArrayList.ArrayListIterator_next_normal.key");
        g.provable("heap/list/ArrayList.ArrayListIterator_pos.key");
        g.provable("heap/list/Client_m.key");
        g.provable("heap/list/Client_n.key");
        g.provable("heap/list/LinkedList_get_exceptional.key");
        g.provable("heap/list/LinkedList_get_normal.key");
        g.provable("heap/list/LinkedList_LinkedList.key");
        g.provable("heap/list/LinkedList_size_dep.key");
        g.provable("heap/list/LinkedList_size.key");
        g.provable("heap/list/MySet_footprint.key");
        g.provable("heap/list/MySet_MySet.key");


        g = c.group("list_ghost");
        g.provable("heap/list_ghost/ArrayList_add.key");
        g.provable("heap/list_ghost/ArrayList_ArrayList.key");
        g.provable("heap/list_ghost/ArrayList_enlarge.key");
        g.provable("heap/list_ghost/ArrayList_get_dep.key");
        g.provable("heap/list_ghost/ArrayList_get_exceptional.key");
        g.provable("heap/list_ghost/ArrayList_get_normal.key");
        g.provable("heap/list_ghost/ArrayList_inv.key");
        g.provable("heap/list_ghost/ArrayList_size_dep.key");
        g.provable("heap/list_ghost/ArrayList_size.key");


        g = c.group("list_recursive");
        g.provable(
            "heap/list_recursiveSpec/ListOperationsNonNull_getNextNN_normal_behavior.key");
        g.provable(
            "heap/list_recursiveSpec/ListOperationsNonNull_setValueAt_normal_behavior.key");
        // Note:
        // This proof was automatic in earlier versions of KeY but the automatic inductions do not
        // work with model methods
        // g.provable("heap/list_recursiveSpec/ListOperationsNonNull_remove_normal_behavior.key");


        g = c.group("list_seq");
        g.provable("heap/list_seq/SimplifiedLinkedList.remove.key");
        g.provable("heap/list_seq/ArrayList.ArrayList.key");
        g.provable("heap/list_seq/ArrayList.add.key");
        g.provable("heap/list_seq/ArrayList.contains.key");
        g.provable("heap/list_seq/ArrayList.enlarge.key");
        g.provable("heap/list_seq/ArrayList.get.key");
        g.provable("heap/list_seq/ArrayList.newArray.key");
        g.provable("heap/list_seq/ArrayList.remove.0.key");
        g.provable("heap/list_seq/ArrayList.remove.1.key");


        g = c.group("observer");
        g.provable("heap/observer/ExampleObserver_ExampleObserver.key");
        g.provable("heap/observer/ExampleObserver_inv.key");
        g.provable("heap/observer/ExampleObserver_subject.key");
        g.provable("heap/observer/ExampleObserver_update.key");
        g.provable("heap/observer/ExampleObserver_upToDate.key");
        g.provable("heap/observer/ExampleObserver_value.key");
        g.provable("heap/observer/ExampleSubject_addObserver.key");
        g.provable("heap/observer/ExampleSubject_change.key");
        g.provable("heap/observer/ExampleSubject_ExampleSubject.key");
        g.provable("heap/observer/ExampleSubject_footprint.key");
        g.provable("heap/observer/ExampleSubject_inv.key");
        g.provable("heap/observer/ExampleSubject_notifyObservers.key");
        g.provable("heap/observer/ExampleSubject_value_dep.key");
        g.provable("heap/observer/ExampleSubject_value.key");


        g = c.group("removeDups");
        g.provable("heap/removeDups/arrayPart.key");
        g.provable("heap/removeDups/contains.key");
        g.provable("heap/removeDups/removeDup.key");


        g.provable("heap/saddleback_search/Saddleback_search.key");

        g = c.group("quicksort");
        g.setLocalSettings("[Choice]DefaultChoices=moreSeqRules-moreSeqRules:on");
        g.setDirectory("heap/quicksort");
        g.provable("toplevel.key");
        g.provable("sort.key");
        g.provable("split.key");


        /*
         * These are simpler regression tests that show a certain feature works
         * fine.
         */
        g = c.group("simpleTests");
        g.provable("heap/simple/anonymise_datagroup.key");
        g.provable("heap/simple/array_creation.key");
        g.provable("heap/simple/arrays_with_disjoint_sorts.key");
        g.provable("heap/simple/arrays.key");
        g.provable("heap/simple/attributes.key");
        g.provable("heap/simple/constructor_contracts.key");
        g.provable("heap/simple/dependencies.key");
        g.provable("heap/simple/dependency_contracts.key");
        g.provable("heap/simple/invariant_preservation.key");
        g.provable("heap/simple/locsets.key");
        g.provable("heap/simple/loop1.key");
        g.provable("heap/simple/loop2.key");
        g.provable("heap/simple/modifies_datagroup.key");
        g.provable("heap/simple/modifies.key");
        g.provable("heap/simple/object_creation.key");
        g.provable("heap/simple/operation_contracts.key");
        g.provable("heap/simple/select_store.key");
        g.provable("heap/simple/selection_sort.key");
        g.provable("heap/simple/seq.key");
        g.provable("heap/simple/oldForParams.key");
        g.provable("heap/simple/parse_lmtd.key");
        g.provable("heap/strictly_pure/strictlyPureMethod.key");
        g.provable("heap/strictly_pure/useStrictlyPureMethod.key");
        g.provable("heap/Wellfounded/ackermann.key");
        g.provable("standard_key/unicode_test.key");
        g.provable("heap/strictlyModular/mayExpand.key");
        g.notprovable("heap/strictlyModular/modularOnly.key");


        g = c.group("SmansEtAl");
        g.provable("heap/SmansEtAl/ArrayList_add.key");
        g.provable("heap/SmansEtAl/ArrayList_ArrayList.key");
        g.provable("heap/SmansEtAl/ArrayList_footprint.key");
        g.provable("heap/SmansEtAl/ArrayList_get_dep.key");
        g.provable("heap/SmansEtAl/ArrayList_get.key");
        g.provable("heap/SmansEtAl/ArrayList_inv.key");
        g.provable("heap/SmansEtAl/ArrayList_size_dep.key");
        g.provable("heap/SmansEtAl/ArrayList_size.key");
        g.provable("heap/SmansEtAl/Cell_Cell.key");
        g.provable("heap/SmansEtAl/Cell_footprint.key");
        g.provable("heap/SmansEtAl/Cell_getX_dep.key");
        g.provable("heap/SmansEtAl/Cell_getX.key");
        g.provable("heap/SmansEtAl/Cell_inv.key");
        g.provable("heap/SmansEtAl/Cell_setX.key");
        g.provable("heap/SmansEtAl/CellClient_m.key");
        g.provable("heap/SmansEtAl/Iterator_footprint.key");
        g.provable("heap/SmansEtAl/Iterator_hasNext_dep.key");
        g.provable("heap/SmansEtAl/Iterator_hasNext.key");
        g.provable("heap/SmansEtAl/Iterator_inv.key");
        g.provable("heap/SmansEtAl/Iterator_Iterator.key");
        g.provable("heap/SmansEtAl/Iterator_list_dep.key");
        g.provable("heap/SmansEtAl/Iterator_list.key");
        g.provable("heap/SmansEtAl/Iterator_next.key");
        g.provable("heap/SmansEtAl/Stack_footprint.key");
        g.provable("heap/SmansEtAl/Stack_inv.key");
        g.provable("heap/SmansEtAl/Stack_push.key");
        g.provable("heap/SmansEtAl/Stack_size.key");
        g.provable("heap/SmansEtAl/Stack_Stack.key");
        g.provable("heap/SmansEtAl/Stack_switchContents.key");


        g = c.group("VACID0");
        g.provable("heap/vacid0_01_SparseArray/Harness_sparseArrayTestHarness1.key");
        g.provable("heap/vacid0_01_SparseArray/Harness_sparseArrayTestHarness2.key");
        g.provable("heap/vacid0_01_SparseArray/MemoryAllocator_alloc_unsigned.key");
        g.provable("heap/vacid0_01_SparseArray/MemoryAllocator_alloc.key");
        g.provable("heap/vacid0_01_SparseArray/SparseArray_get_dep.key");
        g.provable("heap/vacid0_01_SparseArray/SparseArray_get.key");
        g.provable("heap/vacid0_01_SparseArray/SparseArray_inv.key");
        g.provable("heap/vacid0_01_SparseArray/SparseArray_SparseArray.key");


        g = c.group("VSTTE10");
        g.provable("heap/vstte10_01_SumAndMax/SumAndMax_sumAndMax.key");
        g.provable("heap/vstte10_03_LinkedList/Node_cons.key");
        g.provable("heap/vstte10_03_LinkedList/Node_inv.key");
        g.provable("heap/vstte10_03_LinkedList/Node_search.key");
        g.provable("heap/vstte10_04_Queens/Queens_isConsistent.key");
        g.provable("heap/vstte10_04_Queens/Queens_nQueens.key");
        g.provable("heap/vstte10_05_Queue/AmortizedQueue_AmortizedQueue.key");
        g.provable("heap/vstte10_05_Queue/AmortizedQueue_front.key");
        g.provable("heap/vstte10_05_Queue/LinkedList_concat.key");
        g.provable("heap/vstte10_05_Queue/LinkedList_cons.key");
        g.provable("heap/vstte10_05_Queue/LinkedList_head.key");
        g.provable("heap/vstte10_05_Queue/LinkedList_inv.key");
        g.provable("heap/vstte10_05_Queue/LinkedList_length.key");
        g.provable("heap/vstte10_05_Queue/LinkedList_LinkedList1.key");
        g.provable("heap/vstte10_05_Queue/LinkedList_LinkedList2.key");
        g.provable("heap/vstte10_05_Queue/LinkedList_LinkedList3.key");
        g.provable("heap/vstte10_05_Queue/LinkedList_reverse.key");
        g.provable("heap/vstte10_05_Queue/LinkedList_tail.key");


        g = c.group("WeideEtAl");
        g.provable("heap/WeideEtAl_01_AddAndMultiply/AddAndMultiply_add.key");
        g.provable("heap/WeideEtAl_01_AddAndMultiply/AddAndMultiply_mul.key");
        g.provable("heap/WeideEtAl_02_BinarySearch/BinarySearch_search.key");


        // this file contains Unicode symbols for logic operators
        g = c.group("arithmetic");
        g.provable("standard_key/arith/binomial1.key");
        g.provable("standard_key/arith/binomial2.key");
        g.provable("standard_key/arith/check_jdiv.key");
        g.provable("standard_key/arith/check_jdiv_concrete.key");
        g.provable("standard_key/arith/check_jdiv_instantiated.key");
        g.provable("standard_key/arith/check_jmod.key");
        g.provable("standard_key/arith/complexExpressions.key");
        g.provable("standard_key/arith/compound_unaryMinus.key");
        g.provable("standard_key/arith/computation.key");
        g.provable("standard_key/arith/cubicSum.key");
        g.provable("standard_key/arith/divByZero.key");
        g.provable("standard_key/arith/divisionAssoc.key");
        g.provable("standard_key/arith/divisionBy2.key");
        g.provable("standard_key/arith/euclidean/gcdHelp-post.key");
        g.provable("standard_key/arith/gemplusDecimal/add.key");
        g.provable("standard_key/arith/jdivevenodd.key");
        g.provable("standard_key/arith/median.key");
        g.provable("standard_key/arith/mod1.key");
        g.provable("standard_key/arith/mod2.key");
        g.provable("standard_key/arith/mod7.key");
        g.provable("standard_key/arith/overflow_hija.key");
        g.provable("standard_key/arith/poly_division0.key");
        g.provable("standard_key/arith/poly_division1.key");
        g.provable("standard_key/inEqSimp/division.key");
        g.provable("standard_key/inEqSimp/inequations0.key");
        g.provable("standard_key/inEqSimp/inequations1.key");
        g.provable("standard_key/inEqSimp/inequations2.key");
        g.provable("standard_key/inEqSimp/linApprox.key");
        g.provable("standard_key/inEqSimp/nonLinInEqExample0.key");
        g.provable("standard_key/inEqSimp/nonLinInEqExample2.key");
        g.provable("standard_key/inEqSimp/nonLinInEqExample3.key");
        g.provable("standard_key/inEqSimp/nonLinInEqExample4.key");
        g.provable("standard_key/inEqSimp/quadraticInEq.key");
        g.provable("standard_key/inEqSimp/quadraticInEq10.key");
        g.provable("standard_key/inEqSimp/quadraticInEq13.key");
        g.provable("standard_key/inEqSimp/quadraticInEq14.key");
        g.provable("standard_key/inEqSimp/quadraticInEq2.key");
        g.provable("standard_key/inEqSimp/quadraticInEq3.key");
        g.provable("standard_key/inEqSimp/quadraticInEq4.key");
        g.provable("standard_key/inEqSimp/quadraticInEq5.key");
        g.provable("standard_key/inEqSimp/quadraticInEq6.key");
        g.provable("standard_key/inEqSimp/quadraticInEq7.key");
        g.provable("standard_key/inEqSimp/quadraticInEq8.key");
        g.provable("standard_key/inEqSimp/simplify0.key");
        g.provable("standard_key/inEqSimp/simplify1.key");
        g.provable("standard_key/inEqSimp/simplify2.key");
        g.provable("standard_key/inEqSimp/simplify3.key");
        g.provable("standard_key/inEqSimp/simplify4.key");
        g.provable("standard_key/inEqSimp/simplify5.key");
        g.provable("standard_key/inEqSimp/subsumptionExample.key");
        g.provable("standard_key/polySimp/simplify0.key");
        g.provable("standard_key/polySimp/simplify1.key");
        g.provable("standard_key/polySimp/simplify10.key");
        g.provable("standard_key/polySimp/simplify11.key");
        g.provable("standard_key/polySimp/simplify12.key");
        g.provable("standard_key/polySimp/simplify13.key");
        g.provable("standard_key/polySimp/simplify14.key");
        g.provable("standard_key/polySimp/simplify15.key");
        g.provable("standard_key/polySimp/simplify16.key");
        g.provable("standard_key/polySimp/simplify17.key");
        g.provable("standard_key/polySimp/simplify18.key");
        g.provable("standard_key/polySimp/simplify19.key");
        g.provable("standard_key/polySimp/simplify2.key");
        g.provable("standard_key/polySimp/simplify20.key");
        g.provable("standard_key/polySimp/simplify21.key");
        g.provable("standard_key/polySimp/simplify22.key");
        g.provable("standard_key/polySimp/simplify23.key");
        g.provable("standard_key/polySimp/simplify24.key");
        g.provable("standard_key/polySimp/simplify25.key");
        g.provable("standard_key/polySimp/simplify3.key");
        g.provable("standard_key/polySimp/simplify4.key");
        g.provable("standard_key/polySimp/simplify5.key");
        g.provable("standard_key/polySimp/simplify6.key");
        g.provable("standard_key/polySimp/simplify7.key");
        g.provable("standard_key/polySimp/simplify8.key");
        g.provable("standard_key/polySimp/simplify9.key");


        g = c.group("arrays");
        g.provable("standard_key/arrays/arrayStoreException/array2DimPrim.key");
        g.provable("standard_key/arrays/arrayStoreException/arrayStoreKnownDynType.key");
        g.provable("standard_key/arrays/arrayStoreException/reverseArray.key");
        g.provable("standard_key/arrays/arrayStoreException/throwArrayStoreException.key");
        g.provable("standard_key/arrays/creation/arrayCreation1.key");
        g.notprovable("standard_key/arrays/arrayStoreException/array2Dim.key");
        g.notprovable("standard_key/arrays/arrayStoreException/array2DimClose.key");
        g.notprovable("standard_key/arrays/arrayStoreException/throwASEForPrim.key");


        g = c.group("javadl");
        g.provable("standard_key/instanceCreation/instanceCreation1.key");
        g.provable("standard_key/instanceCreation/instanceCreation2.key");
        g.provable(
            "standard_key/instanceCreation/interfacesAndAbstractClassesHaveNoInstances.key");
        g.provable("standard_key/instanceCreation/successiveCreatedObjectsAreDistinct.key");
        g.provable("standard_key/instanceCreation/testOverloadingConstructors.key");
        g.provable("standard_key/java_dl/SimpleAttributes.key");
        g.provable("standard_key/java_dl/arrayMax.key");
        g.provable("standard_key/java_dl/arrayUpdateSimp.key");
        g.provable("standard_key/java_dl/attributes.key");
        g.provable("standard_key/java_dl/break.key");
        g.provable("standard_key/java_dl/char.key");
        g.provable("standard_key/java_dl/compileTimeConstants.key");
        g.provable("standard_key/java_dl/constructorException/test.key");
        g.notprovable("standard_key/java_dl/constructorException/regressionTestBug1333.key");
        g.provable("standard_key/java_dl/continue1.key");
        g.provable("standard_key/java_dl/continue2.key");
        g.provable("standard_key/java_dl/complexAssignment.key");
        g.provable("standard_key/java_dl/danglingElseSolution1.key");
        g.provable("standard_key/java_dl/danglingElseSolution2.key");
        g.provable("standard_key/java_dl/deepNonNull/deepNonNull0.key");
        g.provable("standard_key/java_dl/deepNonNull/deepNonNull1.key");
        g.notprovable("standard_key/java_dl/deepNonNull/deepNonNull2.key");
        g.provable("standard_key/java_dl/deepNonNull/deepNonNull3.key");
        g.provable("standard_key/java_dl/exceptions.key");
        g.provable("standard_key/java_dl/exceptions1.key");
        g.provable("standard_key/java_dl/exceptions2.key");
        g.provable("standard_key/java_dl/exceptions3.key");
        g.provable("standard_key/java_dl/exchange.key");
        g.provable("standard_key/java_dl/if.key");
        g.provable("standard_key/java_dl/incrementcounter.key");
        g.notprovable("standard_key/java_dl/danglingElse.key");
        // commented out -in the current handling of this references(from branch mostThisRef)
        // inner classes do not work.According to Richard, there is a bug in handling inner classes
        // that needs a non -trivial fix.
        // provable: ./standard_key/java_dl/innerClasses/inner.key");
        g.provable("standard_key/java_dl/iteratedAssignment.key");
        g.notprovable("standard_key/java_dl/assert/assert1.key");
        g.provable("standard_key/java_dl/assert/assert2.key");
        g.notprovable("standard_key/java_dl/assert/assert3.key");
        g.provable("standard_key/java_dl/java5/vararg.key");
        g.provable("standard_key/java_dl/java5/for_Array.key");
        g.provable("standard_key/java_dl/java5/for_Iterable.key");
        g.provable("standard_key/java_dl/java5/for_ReferenceArray.key");
        g.provable("standard_key/java_dl/jml-bigint/cast.key");
        g.provable("standard_key/java_dl/jml-free/loopInvFree.key");
        g.provable("standard_key/java_dl/jml-free/ensuresFree.key");
        // proof gets very long
        // requires further investigations
        g.provable("standard_key/java_dl/jml-information-flow.key");
        g.notprovable("standard_key/java_dl/jml-min/min-unprovable1.key");
        g.notprovable("standard_key/java_dl/jml-min/min-unprovable2.key");
        g.provable("standard_key/java_dl/methodCall.key");
        g.provable("standard_key/java_dl/methodCall1.key");
        g.provable("standard_key/java_dl/methodCall1box.key");
        // Commented out as this can not be proved modularly sound (See !183 which is related)
        // g.provable("standard_key/java_dl/methodCall2.key");
        g.provable("standard_key/java_dl/methodCall3.key");
        g.provable("standard_key/java_dl/polishFlagSort.key");
        g.provable("standard_key/java_dl/postConditionTaclets1.key");
        g.provable("standard_key/java_dl/postConditionTaclets2.key");
        g.provable("standard_key/java_dl/quantifiedQuery.key");
        g.provable("standard_key/java_dl/recursion/triangular.key");
        g.provable("standard_key/java_dl/reverseArray.key");
        g.provable("standard_key/java_dl/reverseArray2.key");
        g.provable("standard_key/java_dl/simpleAssignment.key");
        g.provable("standard_key/java_dl/simpleAssignment2.key");
        g.provable("standard_key/java_dl/splittingWithQueries.key");
        g.provable("standard_key/java_dl/strassen/strassen.key");
        g.provable("standard_key/java_dl/symmArray.key");
        g.provable("standard_key/java_dl/testcontext.key");
        g.provable("standard_key/staticInitialisation/cascadeStaticInitialisation.key");
        g.provable(
            "standard_key/staticInitialisation/erroneousClassImpliesErroneousSubclass.key");
        g.provable(
            "standard_key/staticInitialisation/initializedSubclassImpliesInitializedSuperclass.key");
        g.provable("standard_key/staticInitialisation/localDeclared.key");
        g.provable("standard_key/staticInitialisation/localDeclaredMethod.key");
        g.provable("standard_key/staticInitialisation/objectOfErroneousClass.key");
        g.provable("standard_key/staticInitialisation/staticInitialisersAreNonSimple.key");
        g.provable("standard_key/types/disjoint.key");
        g.provable("../../key.core/src/test/resources/testcase/classpath/classpath.key");
        g.notprovable("heap/inconsistent_represents/MyClass_m.key");
        g.notprovable("heap/inconsistent_represents/MyClass_n.key");


        g = c.group("FOL");
        g.provable("standard_key/pred_log/count.key");
        g.provable("standard_key/pred_log/count2.key");
        g.provable("standard_key/pred_log/count3.key");
        g.provable("standard_key/pred_log/equalities.key");
        g.provable("standard_key/pred_log/equalities2.key");
        g.provable("standard_key/pred_log/equalities3.key");
        // cannot be proven automatically (see bug //1248)
        // provable: ./standard_key/pred_log/exist1.key");
        g.provable("standard_key/pred_log/functions.key");
        g.provable("standard_key/pred_log/mv1.key");
        g.provable("standard_key/pred_log/mv2.key");
        g.provable("standard_key/pred_log/quantifiers.key");
        g.provable("standard_key/pred_log/simpleEps.key");
        g.provable("standard_key/pred_log/steam1.key");
        g.provable("standard_key/pred_log/tptp/PUZ/PUZ001p1.key");
        g.provable("standard_key/pred_log/tptp/PUZ/PUZ001p1-eq.key");
        g.provable("standard_key/pred_log/tptp/PUZ/PUZ031p1.key");
        g.provable("standard_key/pred_log/tptp/SET/SET027p3.key");
        g.provable("standard_key/pred_log/tptp/SET/SET043p1.key");
        // cannot be proven automatically (see bug //1248)
        // provable: ./standard_key/pred_log/tptp/SET/SET044p1.key");
        g.provable("standard_key/pred_log/tptp/SET/SET045p1.key");
        g.provable("standard_key/pred_log/tptp/SET/SET062p3.key");
        g.provable("standard_key/pred_log/tptp/SET/SET063p3.key");
        // cannot be proven automatically (see bug //1248)
        // provable: ./standard_key/pred_log/tptp/SYN/SYN002m1 .007 .008.key");
        g.provable("standard_key/pred_log/tptp/SYN/SYN036p2.key");
        // cannot be proven automatically (timeout, possibly due to bug //1248)
        // provable: ./standard_key/pred_log/tptp/SYN/SYN548p1.key");
        g.provable("standard_key/pred_log/tptp/SYN/SYN550p1.key");
        g.notprovable("standard_key/prop_log/reallySimple.key");
        g.notprovable("standard_key/pred_log/sameName1.key");
        g.provable("standard_key/pred_log/jbyteIfEx.key");
        g.provable("standard_key/prop_log/allClausesLength4.key");
        g.provable("standard_key/prop_log/allClausesLength5.key");
        g.provable("standard_key/prop_log/doubleNeg.key");
        g.provable("standard_key/prop_log/liarsville.key");
        g.provable("standard_key/prop_log/simplest.key");
        g.provable("standard_key/prop_log/contraposition.key");
        g.provable("standard_key/quantifiers/elimination0.key");
        g.provable("standard_key/quantifiers/heuristic_PUZ001p1-eq.key");
        g.provable("standard_key/quantifiers/heuristic_PUZ001p1.key");
        g.provable("standard_key/quantifiers/heuristic_PUZ031p1.key");
        g.provable("standard_key/quantifiers/heuristic_SYN036p2.key");
        g.provable("standard_key/quantifiers/injectivity.key");
        g.provable("standard_key/quantifiers/normalisation0.key");
        g.provable("standard_key/quantifiers/normalisation1.key");
        g.provable("standard_key/quantifiers/normalisation2.key");
        g.provable("standard_key/quantifiers/normalisation3.key");
        g.provable("standard_key/quantifiers/normalisation4.key");
        g.provable("standard_key/quantifiers/normalisation5.key");
        g.provable("standard_key/quantifiers/normalisation6.key");
        g.provable("standard_key/quantifiers/normalisation7.key");
        g.provable("standard_key/quantifiers/normalisation8.key");
        g.provable("standard_key/quantifiers/normalisation9.key");
        g.provable("standard_key/quantifiers/normalisation10.key");
        // removed as long as we do not have a rule safely removing identical updates
        // provable: ./standard_key/quantifiers/normalisation11.key");
        g.provable("standard_key/quantifiers/normalisation12.key");
        g.provable("standard_key/quantifiers/normalisation13.key");
        g.provable("standard_key/quantifiers/triggers0.key");


        g = c.group("strings");
        g.provable("standard_key/strings/charAt0.key");
        g.provable("standard_key/strings/charAt1.key");
        g.provable("standard_key/strings/concat1.key");
        g.provable("standard_key/strings/concat2.key");
        g.provable("standard_key/strings/deriveLength1.key");
        g.provable("standard_key/strings/emptyStringLengthZero.key");
        g.provable("standard_key/strings/implicitBooleanStringConversion.key");
        g.provable("standard_key/strings/implicitBooleanStringConversion2.key");
        g.provable("standard_key/strings/implicitIntStringConversion.key");
        g.provable("standard_key/strings/implicitNullStringConversion.key");
        g.provable("standard_key/strings/implicitNullStringConversion2.key");
        g.provable("standard_key/strings/implicitObjectStringConversion.key");
        g.provable("standard_key/strings/literalEquality.key");
        g.provable("standard_key/strings/replace0.key");
        g.provable("standard_key/strings/replace1.key");
        g.provable("standard_key/strings/simpleAssignment.key");
        g.provable("standard_key/strings/simpleLengthComp.key");
        g.provable("standard_key/strings/stringCompileTimeConstant1.key");
        g.provable("standard_key/strings/stringCompileTimeConstant2.key");
        g.provable("standard_key/strings/stringEquality1.key");
        g.provable("standard_key/strings/stringEquality2.key");
        g.provable("standard_key/strings/substring0.key");
        g.provable("standard_key/strings/substring1.key");
        g.provable("standard_key/strings/substring2.key");
        g.provable("standard_key/strings/substring3.key");
        g.provable("standard_key/strings/substring4.key");
        g.provable("standard_key/strings/substring5.key");


        g = c.group("simple_info_flow");
        g.notprovable("heap/information_flow/UpdateAbstraction_ex7_1_insecure.key");
        g.notprovable("heap/information_flow/UpdateAbstraction_ex7_2_insecure.key");


        // Model methods tests:
        // (Note:some of the problems are trivial, but they should be kept
        // here as these problems provide the only test base for model methods)
        g = c.group("modelMethods");
        g.provable("heap/model_methods/Cell_footprint_acc.key");
        g.provable("heap/model_methods/Cell_footprint.key");
        g.provable("heap/model_methods/Cell_get_acc.key");
        g.provable("heap/model_methods/Cell_get.key");
        g.provable("heap/model_methods/Cell_post_set.key");
        g.provable("heap/model_methods/Cell_set.key");
        g.provable("heap/model_methods/CellTest_callSet.key");
        g.provable("heap/model_methods/CellTest_test2.key");
        g.provable("heap/model_methods/CellTest_test.key");
        g.provable("heap/model_methods/Coll1_add.key");
        g.provable("heap/model_methods/Coll1_Coll1_add_pre.key");
        g.provable("heap/model_methods/Coll1_Coll_add_pre.key");
        g.provable("heap/model_methods/Coll2_add.key");
        g.provable("heap/model_methods/Coll2_Coll2_add_pre.key");
        g.provable("heap/model_methods/Coll2_Coll_add_pre.key");
        g.provable("heap/model_methods/Coll_add.key");
        g.provable("heap/model_methods/Coll_add_pre.key");
        g.provable("heap/model_methods/Indirect_callAdd.key");
        g.provable("heap/model_methods/Indirect_test.key");
        g.provable("heap/model_methods/Recell_Cell_footprint.key");
        g.provable("heap/model_methods/Recell_Cell_post_set.key");
        g.provable("heap/model_methods/Recell_footprint_acc.key");
        g.provable("heap/model_methods/Recell_get_acc.key");
        g.provable("heap/model_methods/Recell_get.key");
        g.provable("heap/model_methods/Recell_Recell_footprint.key");
        g.provable("heap/model_methods/Recell_Recell_post_set.key");
        g.provable("heap/model_methods/Recell_set.key");
        g.provable("heap/model_methods/Recell_undo.key");


        // Permission heap problems:
        g = c.group("permissionHeap");
        g.provable("heap/permissions/permissions_method0.key");
        g.provable("heap/permissions/permissions_method1.key");
        g.provable("heap/permissions/permissions_method3.key");
        g.provable("heap/permissions/permissions_setAB.key");
        g.provable("heap/permissions/permissionProperties.key");

        g.provable("heap/permissions/threads/AFilter_AFilter.key");
        g.provable("heap/permissions/threads/AFilter_initPost_accessible.key");
        g.provable("heap/permissions/threads/AFilter_inv_accessible1.key");
        g.provable("heap/permissions/threads/AFilter_inv_accessible2.key");
        g.provable("heap/permissions/threads/AFilter_joinTransfer_accessible.key");
        g.provable("heap/permissions/threads/AFilter_joinTransfer_contract.key");
        g.provable("heap/permissions/threads/AFilter_postJoin_accessible.key");
        g.provable("heap/permissions/threads/AFilter_preStart_accessible.key");
        g.provable("heap/permissions/threads/AFilter_startTransfer_accessible.key");
        g.provable("heap/permissions/threads/AFilter_startTransfer_contract.key");
        g.provable("heap/permissions/threads/AFilter_stateInv_accessible.key");
        g.provable("heap/permissions/threads/AFilter_staticPermissions_accessible.key");
        g.provable("heap/permissions/threads/AFilter_workingPermissions_accessible.key");
        g.provable("heap/permissions/threads/BFilter_BFilter.key");
        g.provable("heap/permissions/threads/BFilter_initPost_accessible.key");
        g.provable("heap/permissions/threads/BFilter_inv_accessible1.key");
        g.provable("heap/permissions/threads/BFilter_inv_accessible2.key");
        g.provable("heap/permissions/threads/BFilter_joinTransfer_accessible.key");
        g.provable("heap/permissions/threads/BFilter_joinTransfer_contract.key");
        g.provable("heap/permissions/threads/BFilter_postJoin_accessible.key");
        g.provable("heap/permissions/threads/BFilter_preStart_accessible.key");
        g.provable("heap/permissions/threads/BFilter_startTransfer_accessible.key");
        g.provable("heap/permissions/threads/BFilter_startTransfer_contract.key");
        g.provable("heap/permissions/threads/BFilter_stateInv_accessible.key");
        g.provable("heap/permissions/threads/BFilter_staticPermissions_accessible.key");
        g.provable("heap/permissions/threads/BFilter_workingPermissions_accessible.key");
        g.provable("heap/permissions/threads/Fib_Fib.key");
        g.provable("heap/permissions/threads/Fib_initPost_accessible.key");
        g.provable("heap/permissions/threads/Fib_inv1_accessible.key");
        g.provable("heap/permissions/threads/Fib_inv2_accessible.key");
        g.provable("heap/permissions/threads/Fib_joinTransfer_accessible.key");
        g.provable("heap/permissions/threads/Fib_joinTransfer_contract.key");
        g.provable("heap/permissions/threads/Fib_postJoin_accessible.key");
        g.provable("heap/permissions/threads/Fib_preStart_accessible.key");
        g.provable("heap/permissions/threads/Fib_startTransfer_accessible.key");
        g.provable("heap/permissions/threads/Fib_startTransfer_contract.key");
        g.provable("heap/permissions/threads/Fib_workingPermissions_accessible.key");
        g.provable("heap/permissions/threads/Plotter_initPost_accessible.key");
        g.provable("heap/permissions/threads/Plotter_inv_accessible1.key");
        g.provable("heap/permissions/threads/Plotter_inv_accessible2.key");
        g.provable("heap/permissions/threads/Plotter_joinTransfer_contract.key");
        g.provable("heap/permissions/threads/Plotter_Plotter.key");
        g.provable("heap/permissions/threads/Plotter_postJoin_accessible.key");
        g.provable("heap/permissions/threads/Plotter_preStart_accessible.key");
        g.provable("heap/permissions/threads/Plotter_stateInv_accessible.key");
        g.provable("heap/permissions/threads/Plotter_staticPermissions_accessible.key");
        g.provable("heap/permissions/threads/Plotter_workingPermissions_accessible.key");
        g.provable("heap/permissions/threads/Sampler_initPost_accessible.key");
        g.provable("heap/permissions/threads/Sampler_inv_accessible1.key");
        g.provable("heap/permissions/threads/Sampler_inv_accessible2.key");
        g.provable("heap/permissions/threads/Sampler_joinTransfer_accessible.key");
        g.provable("heap/permissions/threads/Sampler_joinTransfer_contract.key");
        g.provable("heap/permissions/threads/Sampler_postJoin_accessible.key");
        g.provable("heap/permissions/threads/Sampler_preStart_accessible.key");
        g.provable("heap/permissions/threads/Sampler_run.key");
        g.provable("heap/permissions/threads/Sampler_Sampler.key");
        g.provable("heap/permissions/threads/Sampler_startTransfer_accessible.key");
        g.provable("heap/permissions/threads/Sampler_startTransfer_contract.key");
        g.provable("heap/permissions/threads/Sampler_stateInv_accessible.key");
        g.provable("heap/permissions/threads/Sampler_staticPermissions_accessible.key");
        g.provable("heap/permissions/threads/Sampler_workingPermissions_accessible.key");

        // Müller et al example
        g.provable("heap/permissions/mulleretal/ReadWrite_doRead_contract.key");
        g.provable("heap/permissions/mulleretal/ReadWrite_doWrite_contract.key");
        g.provable("heap/permissions/mulleretal/ReadWrite_read_contract.key");
        g.provable("heap/permissions/mulleretal/ReadWrite_write_contract.key");
        g.provable("heap/permissions/mulleretal/ReadWrite_inv1_accessible.key");
        g.provable("heap/permissions/mulleretal/ReadWrite_inv2_accessible.key");

        // The LockSpec example(permissions & model methods)
        g.provable("heap/permissions/lockspec/Counter_lockConsistent_contract.key");
        g.provable("heap/permissions/lockspec/Counter_increase_contract.key");
        g.provable("heap/permissions/lockspec/Counter_fp_accessible.key");
        g.provable("heap/permissions/lockspec/Counter_fpLock_accessible.key");
        g.provable("heap/permissions/lockspec/Counter_fpPerm_accessible.key");
        g.provable("heap/permissions/lockspec/Counter_inv_accessible1.key");
        g.provable("heap/permissions/lockspec/Counter_inv_accessible2.key");
        g.provable("heap/permissions/lockspec/Counter_lockRef_accessible.key");
        g.provable("heap/permissions/lockspec/Counter_lockRef_contract1.key");
        g.provable("heap/permissions/lockspec/Counter_lockRef_contract2.key");
        g.provable("heap/permissions/lockspec/Counter_lockState_accessible.key");
        g.provable("heap/permissions/lockspec/Counter_lockStatus_accessible.key");
        g.provable("heap/permissions/lockspec/Counter_lockTransfer_accessible.key");
        g.provable("heap/permissions/lockspec/Counter_unlockTransfer_accessible.key");

        // These need (a lot of)interaction at the moment:
        // provable: ./heap/permissions/threads/AFilter_run.key");
        // provable: ./heap/permissions/threads/BFilter_run.key");
        // provable: ./heap/permissions/threads/Fib_run.key");
        // provable: ./heap/permissions/threads/Plotter_run.key");
        // provable: ./heap/permissions/threads/Main_main.key");

        // Is provable, but very heavy (~400000 steps)
        // g.provable("heap/permissions/threads/Plotter_startTransfer_contract.key");
        g.loadable("heap/permissions/threads/Plotter_startTransfer_contract.proof");

        // after !513 no longer g.provable(in automode but the old proofs are still loadable:
        // g.provable("heap/permissions/threads/Plotter_startTransfer_accessible.key");
        g.loadable("heap/permissions/threads/Plotter_startTransfer_accessible.proof");
        // g.provable("heap/permissions/threads/Plotter_joinTransfer_accessible.key");
        g.loadable("heap/permissions/threads/Plotter_joinTransfer_accessible.proof");


        // Completion scopes /Exec statement tests
        g = c.group("completionScopes");
        g.provable("completionscopes/testCcatchReturnVal.key");
        g.provable("completionscopes/testMultCcatchClauses.key");
        g.provable("completionscopes/testNestedExec.key");
        g.provable("completionscopes/testCcatchBreakLabel.key");
        g.provable("completionscopes/testCcatchContinueLabel.key");
        g.provable("completionscopes/testCcatchBreakLabelWildcard.key");
        g.provable("completionscopes/testCcatchContinueLabelWildcard.key");
        g.provable("completionscopes/testCcatchBreakLabelNonmatchingNested.key");


        // These are the proof files which can be loaded from the examples menu.
        // They must work with the current version.
        g = c.group("reload_examples");
        g.provable("firstTouch/05-ReverseArray/reverseArray.key");

        // This is a reload regression test.Since it is the only one
        // it goes here with the sibling reload tests
        g.loadable("standard_key/arith/saveProofTest.key.proof");
        g.loadable("heap/permutedSum/perm.proof");
        g.loadable("firstTouch/05-ReverseArray/reverseArray.proof");
        g.loadable("heap/verifyThis15_1_RelaxedPrefix/relax.proof");
        g.loadable("heap/verifyThis15_3_DLL/doUndo.proof");
        g.loadable("heap/verifyThis15_2_ParallelGcd/parallelGcd.proof");
        // Temporarily disabled, see //1720
        // loadable./heap/verifyThis17_1_PairInsertionSort/sort.proof.gz


        // Test whether reloading works (no examples)
        g = c.group("proofLoadRepair");

        // Demonstrate that loading a manipulated proof with wrong
        // assumes instantiations works(MR !516).
        // Provided that there is a unique candidate to instantiate.
        g.loadable("proofLoadRepair/disjConj-manipulated.proof");

        // There are two possible candidates to instantiate the assumes sequent.
        g.notloadable("proofLoadRepair/insufficient-manipulated.proof");

        // Verify that taclet instantiations read from proof files are checked
        // for correct polarity (Issue //1716).
        g.notloadable(
            "../../key.core/src/test/resources/testcase/issues/1716/incorrectPolarity.proof");
        g.notloadable(
            "../../key.core/src/test/resources/testcase/issues/1716/incorrectPolarity2.proof");
        g.notloadable(
            "../../key.core/src/test/resources/testcase/issues/1716/incorrectPolarity3.proof");


        g = c.group("switch");

        // This isn 't a good test as it depends on ordering and naming scheme
        // but it should be ok as regression test
        // keep as first test in this group
        g.provable("standard_key/java_dl/switch/labeled_case.key");

        g.provable("standard_key/java_dl/switch/empty_switch.key");

        // testing that side effects of the expression matter
        g.provable("standard_key/java_dl/switch/empty_switch_null.key");
        g.provable("standard_key/java_dl/switch/empty_switch_null_catch.key");
        g.provable("standard_key/java_dl/switch/empty_switch_array_out_of_bounds.key");
        g.provable("standard_key/java_dl/switch/empty_switch_array_out_of_bounds_catch.key");

        // test that breaks and labels are handled correctly with nested switches
        g.provable("standard_key/java_dl/switch/switch_in_switch.key");

        g.provable("standard_key/java_dl/switch/while_and_switch.key");

        // this is to test that proving large switch statements are reasonable fast
        g.provable("standard_key/java_dl/switch/large_switch.key");


        g = c.group("redux");
        g.provable("redux/arrays/Arrays.copyOf.key");
        g.provable("redux/arrays/Arrays.copyOf.float.key");
        g.provable("redux/arrays/Arrays.copyOfRange.key");
        g.provable("redux/arrays/Arrays.copyOfRange.float.key");
        g.provable("redux/arrays/Arrays.equals.key");
        g.provable("redux/arrays/Arrays.fill.key");
        g.provable("redux/arrays/Arrays.fill.float.key");
        g.provable("redux/arrays/Arrays.fillFromTo.key");
        g.provable("redux/arrays/Arrays.fillFromTo.float.key");
        g.provable("redux/arrays/ArrayCopy.arraycopy.normal.0.key");
        g.provable("redux/arrays/ArrayCopy.arraycopy.exceptional.0.key");
        g.provable("redux/arrays/ArrayCopy.arraycopy.exceptional.1.key");

        return c;
    }


    public static ProofCollection automaticInfFlow() throws IOException {
        var settings = new ProofCollectionSettings(new Date());
        var c = new ProofCollection(settings);
        /*
         * Defines a base directory.
         * All paths in this file are treated relative to base directory (except path for base
         * directory itself).
         */
        settings.setBaseDirectory("../key.ui/examples/InformationFlow/");

        /*
         * Defines a statistics file.
         * Path is relative to base directory.
         */
        settings.setStatisticsFile(
            "build/reports/runallproofs/runStatistics_infflow.csv");

        /*
         * Fork mode setting, can be declared to create subprocesses while running tests declared in
         * this file.
         * Possible modes: noFork-all files are proven within a single process
         * perg = c.group("- one subprocess is created for each group
         * perFile-one subprocess is created for each file
         */
        settings.setForkMode(ForkMode.PERGROUP);

        /*
         * Enable or disable proof reloading.
         * If enabled, closed proofs will be saved and reloaded after prover is finished.
         */
        settings.setReloadEnabled(false);

        /*
         * Temporary directory, which is used for inter process communication when using forked
         * mode.
         * The given path is relative to baseDirectory.
         */
        settings.setTempDir("build/runallproofs_infflow_tmp");

        /*
         * If the fork mode is not set to noFork, the launched subprocesses are terminated as
         * soon as the timeout specified here has elapsed. No timeout occurs if not specified.
         *
         * Timeout per subprocess in seconds
         */
        settings.setForkTimeout(1000);

        /*
         * If the fork mode is not set to noFork, the launched subprocesses
         * get the specified amount of heap memory.
         *
         * Heap memory for subprocesses (like 500m or 2G)
         */
        // forkMemory = 1000m

        /*
         * By default runAllProofs does not print a lot of information.
         * Set this to true to get more output.
         */
        settings.setVerboseOutput(true);

        /*
         * By default, runAllProofs runs all groups in this file.
         * By naming a comma separated list of groups here, the
         * test can be restricted to these groups (for debugging).
         */
        // runOnlyOn = group1,group2

        // // Tests for information flow

        var g = c.group("ToyVoting");
        g.provable(
            "ToyVoting/Voter(Voter__insecure_voting()).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyVoting/Voter(Voter__publishVoterParticipation()).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyVoting/Voter(Voter__isValid(int)).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyVoting/Voter(Voter__sendVote(int)).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyVoting/Voter(Voter__inputVote()).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyVoting/Voter(Voter__secure_voting()).JML normal_behavior operation contract.0.key");


        g = c.group("ConditionalConfidential");
        g.provable(
            "ConditionalConfidential/CCExample(CCExample__hasAccessRight(CCExample.User)).JML normal_behavior operation contract.0.key");
        g.provable(
            "ConditionalConfidential/CCExample(CCExample__getConfidentialData(CCExample.User)).JML normal_behavior operation contract.0.key");


        g = c.group("SumExample");
        g.provable(
            "Sum/SumExample(SumExample__getSum()).JML normal_behavior operation contract.0.key");


        g = c.group("ToyBanking");
        g.provable(
            "ToyBanking/banking_example.UserAccount(banking_example.UserAccount__getBankAccount(int)).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyBanking/banking_example.UserAccount(banking_example.UserAccount__tryLogin(int,(C)).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyBanking/banking_example.UserAccount(java.lang.Object___inv_()).JML accessible clause.0.key");
        g.provable(
            "ToyBanking/banking_example.BankAccount(banking_example.BankAccount__depositMoney(int)).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyBanking/banking_example.BankAccount(banking_example.BankAccount__getBalance()).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyBanking/banking_example.BankAccount(banking_example.BankAccount__getId()).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyBanking/banking_example.Bank(banking_example.Bank__login(int,(C)).JML normal_behavior operation contract.0.key");

        g.provable(
            "ToyBanking/banking_example2.UserAccount(banking_example2.UserAccount__getBankAccount(int)).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyBanking/banking_example2.UserAccount(banking_example2.UserAccount__tryLogin(int,(C)).JML normal_behavior operation contract.0.key");
        g.notprovable(
            "ToyBanking/banking_example2.UserAccount(java.lang.Object___inv_()).JML accessible clause.0.key");
        g.provable(
            "ToyBanking/banking_example2.BankAccount(banking_example2.BankAccount__depositMoney(int)).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyBanking/banking_example2.BankAccount(banking_example2.BankAccount__getBalance()).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyBanking/banking_example2.BankAccount(banking_example2.BankAccount__getId()).JML normal_behavior operation contract.0.key");
        g.provable(
            "ToyBanking/banking_example2.Bank(banking_example2.Bank__login(int,(C)).JML normal_behavior operation contract.0.key");


        g = c.group("BlockContracts");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_5()).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__block_no_return_secure(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__while_block_insecure(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__while_block_secure(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__block_while_secure(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__insecure_4(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__insecure_3(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_3(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_2(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_8(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_7(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_6(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__insecure_1(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_4(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_1(int)).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFEfficiencyExamples(contract.IFEfficiencyExamples__mWithoutBlockContract()).JML operation contract.0.key");
        g.provable(
            "BlockContracts/contract.IFEfficiencyExamples(contract.IFEfficiencyExamples__mWithBlockContract()).JML operation contract.0.key");


        g = c.group("MethodContracts");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_recursion_2((I,int)).JML normal_behavior operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_recursion(int)).JML normal_behavior operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_catch_exception()).JML operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n6()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_n6()).JML operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_array_param_helper()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_array_param((I,int)).JML operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n9()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_assignment_0_n9()).JML operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__insecure_if_high_n5_n1()).JML operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n5(int)).JML normal_behavior operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_if_high_n5_n1()).JML operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_if_high_n1()).JML operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_n5()).JML operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n4()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n3()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_sequential_n3_precond_n4()).JML operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__insecure_assignment_n2()).JML operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_assignments_n2()).JML operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n2()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n1()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_sequential_n1_n2()).JML operation contract.0.key");


        g = c.group("LoopInvariants");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_while_3(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_while_2(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_while_4(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_doubleNestedWhile2(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_doubleNestedWhile(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_doubleNestedWhile(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_nestedTwoWhile(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_nestedWhile(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__notSecure_while(int)).JML operation contract.0.key");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__notSecure_while_wrongInv(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_twoWhile(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_twoWhile_2(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_twoWhile(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__loc_secure_while(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_while(int)).JML operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__print(int)).JML normal_behavior operation contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__hammer(int)).JML normal_behavior operation contract.0.key");


        g = c.group("MiniExamples");
        g.provable(
            "MiniExamples/mini.AliasingExamples(mini.AliasingExamples__insecure_1(mini.AliasingExamples,mini.AliasingExamples,int)).JML operation contract.0.key");
        g.provable(
            "MiniExamples/mini.AliasingExamples(mini.AliasingExamples__secure_1(mini.AliasingExamples,mini.AliasingExamples,int)).JML operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_6()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_5()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_4()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_3()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_2()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_1()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.DifferenceSeqLocset(mini.DifferenceSeqLocset__m()).JML normal_behavior operation contract.1.key");
        g.provable(
            "MiniExamples/mini.DifferenceSeqLocset(mini.DifferenceSeqLocset__m()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_8()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_parameter(int)).JML operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_7()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__insecure_p2_2()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_6()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_5()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_4()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_3()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_2()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_1()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__insecure_p2_1()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_6()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_5()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_4()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_3()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_2()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_1()).JML normal_behavior operation contract.1.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_1()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__insecure_p1_2()).JML normal_behavior operation contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__insecure_p1_1()).JML normal_behavior operation contract.0.key");


        g = c.group("NewObjects");
        g.provable(
            "NewObjects/object.AmtoftBanerjee3(object.AmtoftBanerjee3__m()).JML operation contract.0.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee(object.AmtoftBanerjee__m_2()).JML normal_behavior operation contract.0.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee(object.AmtoftBanerjee__m_1()).JML normal_behavior operation contract.1.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee(object.AmtoftBanerjee__m_1()).JML normal_behavior operation contract.0.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee(object.AmtoftBanerjee__getQ()).JML normal_behavior operation contract.0.key");
        g.provable(
            "NewObjects/object.Naumann(object.Naumann__Pair_m(int,int)).JML operation contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_while_i((Ljava.lang.Object)).JML operation contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_method_call()).JML operation contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__if_two_object_creation_next()).JML operation contract.1.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__if_two_object_creation_next()).JML operation contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_if_two_object_creation()).JML operation contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__insecure_two_object_creation()).JML operation contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_two_object_creation()).JML normal_behavior operation contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__insecure_object_assignment()).JML operation contract.1.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__insecure_object_assignment()).JML operation contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_object_creation_3()).JML operation contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_object_creation_2()).JML operation contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_object_creation()).JML operation contract.0.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee2(object.AmtoftBanerjee2__expensive(int)).JML accessible clause.0.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee2(object.AmtoftBanerjee2__expensive(int)).JML normal_behavior operation contract.0.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee2(object.AmtoftBanerjee2__cexp(int)).JML normal_behavior operation contract.0.key");


        g.notprovable(
            "PasswordFile/passwordfile.SecurePasswordFile(passwordfile.SecurePasswordFile___userIndex()).JML accessible clause.0.key");

        g = c.group("SimpleEvoting");
        g.provable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedOutputMessage((B)).JML normal_behavior operation contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedInputMessage((B)).JML normal_behavior operation contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedInputMessage()).JML normal_behavior operation contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedOutput(int)).JML normal_behavior operation contract.0.key");
        g.notprovable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedInput(int)).JML normal_behavior operation contract.0.key");
        g.notprovable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedInput()).JML normal_behavior operation contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment___rep()).JML accessible clause.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.SMT(simple_evoting.SMT__send(simple_evoting.Message,int,simple_evoting.Server)).JML normal_behavior operation contract.1.key");
        g.provable(
            "SimpleEvoting/simple_evoting.SMT(simple_evoting.SMT__send(simple_evoting.Message,int,simple_evoting.Server)).JML normal_behavior operation contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Message(java.lang.Object___inv_()).JML accessible clause.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Server(simple_evoting.Server__resultReady()).JML accessible clause.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Server(simple_evoting.Server__resultReady()).JML normal_behavior operation contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Server(simple_evoting.Server__onSendResult()).JML normal_behavior operation contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Server(simple_evoting.Server__onCollectBallot(simple_evoting.Message)).JML normal_behavior operation contract.1.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Server(simple_evoting.Server__onCollectBallot(simple_evoting.Message)).JML normal_behavior operation contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Server(java.lang.Object___inv_()).JML accessible clause.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.SMTEnv(simple_evoting.SMTEnv__send(int,int,int,simple_evoting.Server,int)).JML normal_behavior operation contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.NetworkClient(simple_evoting.NetworkClient__send((B,simple_evoting.Server,int)).JML normal_behavior operation contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Setup(simple_evoting.Setup__publishResult()).JML normal_behavior operation contract.0.key");
        g.notprovable(
            "SimpleEvoting/simple_evoting.Setup(simple_evoting.Setup__main()).JML normal_behavior operation contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Setup(java.lang.Object___inv_()).JML accessible clause.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Voter(simple_evoting.Voter__onSendBallot(simple_evoting.Server)).JML normal_behavior operation contract.1.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Voter(simple_evoting.Voter__onSendBallot(simple_evoting.Server)).JML normal_behavior operation contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Voter(java.lang.Object___inv_()).JML accessible clause.0.key");


        // // Tests for information flow to be executed without information flow proof macro

        g = c.group("ToyVoting_nomacro");
        g.notprovable("ToyVoting/Voter(Voter__insecure_voting()).Non-interference contract.0.key");
        g.provable(
            "ToyVoting/Voter(Voter__publishVoterParticipation()).Non-interference contract.0.key");
        g.provable("ToyVoting/Voter(Voter__isValid(int)).Non-interference contract.0.key");
        g.provable("ToyVoting/Voter(Voter__sendVote(int)).Non-interference contract.0.key");
        g.provable("ToyVoting/Voter(Voter__inputVote()).Non-interference contract.0.key");
        // g.provable("ToyVoting/Voter(Voter__secure_voting()).Non-interference contract.0.key");


        g = c.group("ConditionalConfidential_nomacro");
        // g.provable("ConditionalConfidential/CCExample(CCExample__getConfidentialData(CCExample.User)).Non-interference
        // contract.0.key");


        g = c.group("SumExample_nomacro");
        g.provable("Sum/SumExample(SumExample__getSum()).Non-interference contract.0.key");


        g = c.group("ToyBanking_nomacro");
        g.provable(
            "ToyBanking/banking_example.UserAccount(banking_example.UserAccount__getBankAccount(int)).Non-interference contract.0.key");
        // g.provable("ToyBanking/banking_example.UserAccount(banking_example.UserAccount__tryLogin(int,(C)).Non-interference
        // contract.0.key");
        g.provable(
            "ToyBanking/banking_example.BankAccount(banking_example.BankAccount__depositMoney(int)).Non-interference contract.0.key");
        g.provable(
            "ToyBanking/banking_example.BankAccount(banking_example.BankAccount__getBalance()).Non-interference contract.0.key");
        g.provable(
            "ToyBanking/banking_example.BankAccount(banking_example.BankAccount__getId()).Non-interference contract.0.key");
        g.notprovable(
            "ToyBanking/banking_example.Bank(banking_example.Bank__login(int,(C)).Non-interference contract.0.key");
        g.provable(
            "ToyBanking/banking_example2.UserAccount(banking_example2.UserAccount__getBankAccount(int)).Non-interference contract.0.key");
        // g.provable("ToyBanking/banking_example2.UserAccount(banking_example2.UserAccount__tryLogin(int,(C)).Non-interference
        // contract.0.key");
        g.provable(
            "ToyBanking/banking_example2.BankAccount(banking_example2.BankAccount__depositMoney(int)).Non-interference contract.0.key");
        g.provable(
            "ToyBanking/banking_example2.BankAccount(banking_example2.BankAccount__getBalance()).Non-interference contract.0.key");
        g.provable(
            "ToyBanking/banking_example2.BankAccount(banking_example2.BankAccount__getId()).Non-interference contract.0.key");
        // g.provable("ToyBanking/banking_example2.Bank(banking_example2.Bank__login(int,(C)).Non-interference
        // contract.0.key");


        g = c.group("BlockContracts_nomacro");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_5()).Non-interference contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__block_no_return_secure(int)).Non-interference contract.0.key");
        g.notprovable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__while_block_insecure(int)).Non-interference contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__while_block_secure(int)).Non-interference contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__block_while_secure(int)).Non-interference contract.0.key");
        g.notprovable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__insecure_4(int)).Non-interference contract.0.key");
        g.notprovable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__insecure_3(int)).Non-interference contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_3(int)).Non-interference contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_2(int)).Non-interference contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_8(int)).Non-interference contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_7(int)).Non-interference contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_6(int)).Non-interference contract.0.key");
        g.notprovable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__insecure_1(int)).Non-interference contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_4(int)).Non-interference contract.0.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_1(int)).Non-interference contract.0.key");
        g.provable(
            "BlockContracts/contract.IFEfficiencyExamples(contract.IFEfficiencyExamples__mWithoutBlockContract()).Non-interference contract.0.key");
        g.provable(
            "BlockContracts/contract.IFEfficiencyExamples(contract.IFEfficiencyExamples__mWithBlockContract()).Non-interference contract.0.key");


        g = c.group("MethodContracts_nomacro");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_recursion_2((I,int)).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_recursion(int)).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_catch_exception()).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n6()).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_n6()).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_array_param((I,int)).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_assignment_0_n9()).Non-interference contract.0.key");
        g.notprovable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__insecure_if_high_n5_n1()).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n5(int)).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_if_high_n5_n1()).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_if_high_n1()).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_n5()).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n4()).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n3()).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_sequential_n3_precond_n4()).Non-interference contract.0.key");
        g.notprovable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__insecure_assignment_n2()).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_assignments_n2()).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n2()).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n1()).Non-interference contract.0.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_sequential_n1_n2()).Non-interference contract.0.key");


        g = c.group("LoopInvariants_nomacro");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_while_3(int)).Non-interference contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_while_2(int)).Non-interference contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_while_4(int)).Non-interference contract.0.key");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_doubleNestedWhile2(int)).Non-interference contract.0.key");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_doubleNestedWhile(int)).Non-interference contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_doubleNestedWhile(int)).Non-interference contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_nestedTwoWhile(int)).Non-interference contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_nestedWhile(int)).Non-interference contract.0.key");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__notSecure_while(int)).Non-interference contract.0.key");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__notSecure_while_wrongInv(int)).Non-interference contract.0.key");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_twoWhile(int)).Non-interference contract.0.key");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_twoWhile_2(int)).Non-interference contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_twoWhile(int)).Non-interference contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__loc_secure_while(int)).Non-interference contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_while(int)).Non-interference contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__print(int)).Non-interference contract.0.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__hammer(int)).Non-interference contract.0.key");


        g = c.group("MiniExamples_nomacro");
        g.notprovable(
            "MiniExamples/mini.AliasingExamples(mini.AliasingExamples__insecure_1(mini.AliasingExamples,mini.AliasingExamples,int)).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.AliasingExamples(mini.AliasingExamples__secure_1(mini.AliasingExamples,mini.AliasingExamples,int)).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_6()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_5()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_4()).Non-interference contract.0.key");
        g.notprovable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_3()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_2()).Non-interference contract.0.key");
        g.notprovable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_1()).Non-interference contract.0.key");
        g.notprovable(
            "MiniExamples/mini.DifferenceSeqLocset(mini.DifferenceSeqLocset__m()).Non-interference contract.1.key");
        g.notprovable(
            "MiniExamples/mini.DifferenceSeqLocset(mini.DifferenceSeqLocset__m()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_8()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_parameter(int)).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_7()).Non-interference contract.0.key");
        g.notprovable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__insecure_p2_2()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_6()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_5()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_4()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_3()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_2()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_1()).Non-interference contract.0.key");
        g.notprovable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__insecure_p2_1()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_6()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_5()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_4()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_3()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_2()).Non-interference contract.0.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_1()).Non-interference contract.1.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_1()).Non-interference contract.0.key");
        g.notprovable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__insecure_p1_2()).Non-interference contract.0.key");
        g.notprovable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__insecure_p1_1()).Non-interference contract.0.key");


        g = c.group("NewObjects_nomacro");
        g.provable(
            "NewObjects/object.AmtoftBanerjee3(object.AmtoftBanerjee3__m()).Non-interference contract.0.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee(object.AmtoftBanerjee__m_2()).Non-interference contract.0.key");
        g.notprovable(
            "NewObjects/object.AmtoftBanerjee(object.AmtoftBanerjee__m_1()).Non-interference contract.1.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee(object.AmtoftBanerjee__m_1()).Non-interference contract.0.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee(object.AmtoftBanerjee__getQ()).Non-interference contract.0.key");
        // g.provable("NewObjects/object.Naumann(object.Naumann__Pair_m(int,int)).Non-interference
        // contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_while_i((Ljava.lang.Object)).Non-interference contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_method_call()).Non-interference contract.0.key");
        g.notprovable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__if_two_object_creation_next()).Non-interference contract.1.key");
        // g.provable("NewObjects/object.ObjectOrientation(object.ObjectOrientation__if_two_object_creation_next()).Non-interference
        // contract.0.key");
        // g.provable("NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_if_two_object_creation()).Non-interference
        // contract.0.key");
        g.notprovable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__insecure_two_object_creation()).Non-interference contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_two_object_creation()).Non-interference contract.0.key");
        g.notprovable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__insecure_object_assignment()).Non-interference contract.1.key");
        g.notprovable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__insecure_object_assignment()).Non-interference contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_object_creation_3()).Non-interference contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_object_creation_2()).Non-interference contract.0.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_object_creation()).Non-interference contract.0.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee2(object.AmtoftBanerjee2__expensive(int)).Non-interference contract.0.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee2(object.AmtoftBanerjee2__cexp(int)).Non-interference contract.0.key");


        g = c.group("SimpleEvoting_nomacro");
        g.provable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedOutputMessage((B)).Non-interference contract.0.key");
        // g.provable("SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedInputMessage((B)).Non-interference
        // contract.0.key");
        // g.provable("SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedInputMessage()).Non-interference
        // contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedOutput(int)).Non-interference contract.0.key");
        g.notprovable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedInput(int)).Non-interference contract.0.key");
        g.notprovable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedInput()).Non-interference contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.SMT(simple_evoting.SMT__send(simple_evoting.Message,int,simple_evoting.Server)).Non-interference contract.1.key");
        g.provable(
            "SimpleEvoting/simple_evoting.SMT(simple_evoting.SMT__send(simple_evoting.Message,int,simple_evoting.Server)).Non-interference contract.0.key");
        // g.provable("SimpleEvoting/simple_evoting.SMTEnv(simple_evoting.SMTEnv__send(int,int,int,simple_evoting.Server,int)).Non-interference
        // contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.NetworkClient(simple_evoting.NetworkClient__send((B,simple_evoting.Server,int)).Non-interference contract.0.key");
        // g.provable("SimpleEvoting/simple_evoting.Setup(simple_evoting.Setup__publishResult()).Non-interference
        // contract.0.key");
        // g.provable("SimpleEvoting/simple_evoting.Setup(simple_evoting.Setup__main()).Non-interference
        // contract.0.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Voter(simple_evoting.Voter__onSendBallot(simple_evoting.Server)).Non-interference contract.1.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Voter(simple_evoting.Voter__onSendBallot(simple_evoting.Server)).Non-interference contract.0.key");


        // // Tests for information flow to be executed with information flow proof macro
        // "FullInformationFlowAutoPilotMacro"

        g = c.group("ToyVoting_fullmacro");
        g.notprovable(
            "ToyVoting/Voter(Voter__insecure_voting()).Non-interference contract.0.m.key");
        g.provable(
            "ToyVoting/Voter(Voter__publishVoterParticipation()).Non-interference contract.0.m.key");
        g.provable("ToyVoting/Voter(Voter__isValid(int)).Non-interference contract.0.m.key");
        g.provable("ToyVoting/Voter(Voter__sendVote(int)).Non-interference contract.0.m.key");
        g.provable("ToyVoting/Voter(Voter__inputVote()).Non-interference contract.0.m.key");
        g.provable("ToyVoting/Voter(Voter__secure_voting()).Non-interference contract.0.m.key");


        // g.provable("ConditionalConfidential/CCExample(CCExample__getConfidentialData(CCExample.User)).Non-interference
        // contract.0.m.key");

        g = c.group("SumExample_fullmacro");
        g.provable("Sum/SumExample(SumExample__getSum()).Non-interference contract.0.m.key");


        g = c.group("ToyBanking_fullmacro");
        g.provable(
            "ToyBanking/banking_example.UserAccount(banking_example.UserAccount__getBankAccount(int)).Non-interference contract.0.m.key");
        g.provable(
            "ToyBanking/banking_example.UserAccount(banking_example.UserAccount__tryLogin(int,(C)).Non-interference contract.0.m.key");
        g.provable(
            "ToyBanking/banking_example.BankAccount(banking_example.BankAccount__depositMoney(int)).Non-interference contract.0.m.key");
        g.provable(
            "ToyBanking/banking_example.BankAccount(banking_example.BankAccount__getBalance()).Non-interference contract.0.m.key");
        g.provable(
            "ToyBanking/banking_example.BankAccount(banking_example.BankAccount__getId()).Non-interference contract.0.m.key");
        g.notprovable(
            "ToyBanking/banking_example.Bank(banking_example.Bank__login(int,(C)).Non-interference contract.0.m.key");
        g.provable(
            "ToyBanking/banking_example2.UserAccount(banking_example2.UserAccount__getBankAccount(int)).Non-interference contract.0.m.key");
        g.provable(
            "ToyBanking/banking_example2.UserAccount(banking_example2.UserAccount__tryLogin(int,(C)).Non-interference contract.0.m.key");
        g.provable(
            "ToyBanking/banking_example2.BankAccount(banking_example2.BankAccount__depositMoney(int)).Non-interference contract.0.m.key");
        g.provable(
            "ToyBanking/banking_example2.BankAccount(banking_example2.BankAccount__getBalance()).Non-interference contract.0.m.key");
        g.provable(
            "ToyBanking/banking_example2.BankAccount(banking_example2.BankAccount__getId()).Non-interference contract.0.m.key");
        // g.provable("ToyBanking/banking_example2.Bank(banking_example2.Bank__login(int,(C)).Non-interference
        // contract.0.m.key");


        g = c.group("BlockContracts_fullmacro");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_5()).Non-interference contract.0.m.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__block_no_return_secure(int)).Non-interference contract.0.m.key");
        g.notprovable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__while_block_insecure(int)).Non-interference contract.0.m.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__while_block_secure(int)).Non-interference contract.0.m.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__block_while_secure(int)).Non-interference contract.0.m.key");
        g.notprovable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__insecure_4(int)).Non-interference contract.0.m.key");
        g.notprovable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__insecure_3(int)).Non-interference contract.0.m.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_3(int)).Non-interference contract.0.m.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_2(int)).Non-interference contract.0.m.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_8(int)).Non-interference contract.0.m.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_7(int)).Non-interference contract.0.m.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_6(int)).Non-interference contract.0.m.key");
        g.notprovable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__insecure_1(int)).Non-interference contract.0.m.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_4(int)).Non-interference contract.0.m.key");
        g.provable(
            "BlockContracts/contract.IFBlockExamples(contract.IFBlockExamples__secure_1(int)).Non-interference contract.0.m.key");
        g.provable(
            "BlockContracts/contract.IFEfficiencyExamples(contract.IFEfficiencyExamples__mWithoutBlockContract()).Non-interference contract.0.m.key");
        g.provable(
            "BlockContracts/contract.IFEfficiencyExamples(contract.IFEfficiencyExamples__mWithBlockContract()).Non-interference contract.0.m.key");


        g = c.group("MethodContracts_fullmacro");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_recursion_2((I,int)).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_recursion(int)).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_catch_exception()).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n6()).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_n6()).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_array_param((I,int)).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_assignment_0_n9()).Non-interference contract.0.m.key");
        g.notprovable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__insecure_if_high_n5_n1()).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n5(int)).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_if_high_n5_n1()).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_if_high_n1()).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_n5()).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n4()).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n3()).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_sequential_n3_precond_n4()).Non-interference contract.0.m.key");
        g.notprovable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__insecure_assignment_n2()).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_assignments_n2()).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n2()).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__n1()).Non-interference contract.0.m.key");
        g.provable(
            "MethodContracts/contract.IFMethodContract(contract.IFMethodContract__secure_sequential_n1_n2()).Non-interference contract.0.m.key");


        g = c.group("InformationFlow_fullmacro");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_while_3(int)).Non-interference contract.0.m.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_while_2(int)).Non-interference contract.0.m.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_while_4(int)).Non-interference contract.0.m.key");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_doubleNestedWhile2(int)).Non-interference contract.0.m.key");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_doubleNestedWhile(int)).Non-interference contract.0.m.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_doubleNestedWhile(int)).Non-interference contract.0.m.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_nestedTwoWhile(int)).Non-interference contract.0.m.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_nestedWhile(int)).Non-interference contract.0.m.key");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__notSecure_while(int)).Non-interference contract.0.m.key");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__notSecure_while_wrongInv(int)).Non-interference contract.0.m.key");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_twoWhile(int)).Non-interference contract.0.m.key");
        g.notprovable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__insecure_twoWhile_2(int)).Non-interference contract.0.m.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_twoWhile(int)).Non-interference contract.0.m.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__loc_secure_while(int)).Non-interference contract.0.m.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__secure_while(int)).Non-interference contract.0.m.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__print(int)).Non-interference contract.0.m.key");
        g.provable(
            "LoopInvariants/loop.IFLoopExamples(loop.IFLoopExamples__hammer(int)).Non-interference contract.0.m.key");

        g = c.group("MiniExamples_fullmacro");
        g.notprovable(
            "MiniExamples/mini.AliasingExamples(mini.AliasingExamples__insecure_1(mini.AliasingExamples,mini.AliasingExamples,int)).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.AliasingExamples(mini.AliasingExamples__secure_1(mini.AliasingExamples,mini.AliasingExamples,int)).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_6()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_5()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_4()).Non-interference contract.0.m.key");
        g.notprovable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_3()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_2()).Non-interference contract.0.m.key");
        g.notprovable(
            "MiniExamples/mini.MiniExamplesLecture(mini.MiniExamplesLecture__m_1()).Non-interference contract.0.m.key");
        g.notprovable(
            "MiniExamples/mini.DifferenceSeqLocset(mini.DifferenceSeqLocset__m()).Non-interference contract.1.m.key");
        g.notprovable(
            "MiniExamples/mini.DifferenceSeqLocset(mini.DifferenceSeqLocset__m()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_8()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_parameter(int)).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_7()).Non-interference contract.0.m.key");
        g.notprovable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__insecure_p2_2()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_6()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_5()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_4()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_3()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_2()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p2_1()).Non-interference contract.0.m.key");
        g.notprovable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__insecure_p2_1()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_6()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_5()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_4()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_3()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_2()).Non-interference contract.0.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_1()).Non-interference contract.1.m.key");
        g.provable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__secure_p1_1()).Non-interference contract.0.m.key");
        g.notprovable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__insecure_p1_2()).Non-interference contract.0.m.key");
        g.notprovable(
            "MiniExamples/mini.MiniExamples(mini.MiniExamples__insecure_p1_1()).Non-interference contract.0.m.key");

        g = c.group("NewObjects_fullmacro");
        g.provable(
            "NewObjects/object.AmtoftBanerjee3(object.AmtoftBanerjee3__m()).Non-interference contract.0.m.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee(object.AmtoftBanerjee__m_2()).Non-interference contract.0.m.key");
        g.notprovable(
            "NewObjects/object.AmtoftBanerjee(object.AmtoftBanerjee__m_1()).Non-interference contract.1.m.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee(object.AmtoftBanerjee__m_1()).Non-interference contract.0.m.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee(object.AmtoftBanerjee__getQ()).Non-interference contract.0.m.key");
        g.provable(
            "NewObjects/object.Naumann(object.Naumann__Pair_m(int,int)).Non-interference contract.0.m.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_while_i((Ljava.lang.Object)).Non-interference contract.0.m.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_method_call()).Non-interference contract.0.m.key");
        g.notprovable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__if_two_object_creation_next()).Non-interference contract.1.m.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__if_two_object_creation_next()).Non-interference contract.0.m.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_if_two_object_creation()).Non-interference contract.0.m.key");
        g.notprovable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__insecure_two_object_creation()).Non-interference contract.0.m.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_two_object_creation()).Non-interference contract.0.m.key");
        g.notprovable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__insecure_object_assignment()).Non-interference contract.1.m.key");
        g.notprovable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__insecure_object_assignment()).Non-interference contract.0.m.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_object_creation_3()).Non-interference contract.0.m.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_object_creation_2()).Non-interference contract.0.m.key");
        g.provable(
            "NewObjects/object.ObjectOrientation(object.ObjectOrientation__secure_object_creation()).Non-interference contract.0.m.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee2(object.AmtoftBanerjee2__expensive(int)).Non-interference contract.0.m.key");
        g.provable(
            "NewObjects/object.AmtoftBanerjee2(object.AmtoftBanerjee2__cexp(int)).Non-interference contract.0.m.key");

        g = c.group("SimpleEvoting_fullmacro");
        g.provable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedOutputMessage((B)).Non-interference contract.0.m.key");
        // g.provable(
        // "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedInputMessage((B)).Non-interference
        // contract.0.m.key"););
        g.provable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedInputMessage()).Non-interference contract.0.m.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedOutput(int)).Non-interference contract.0.m.key");
        g.notprovable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedInput(int)).Non-interference contract.0.m.key");
        g.notprovable(
            "SimpleEvoting/simple_evoting.Environment(simple_evoting.Environment__untrustedInput()).Non-interference contract.0.m.key");
        g.provable(
            "SimpleEvoting/simple_evoting.SMT(simple_evoting.SMT__send(simple_evoting.Message,int,simple_evoting.Server)).Non-interference contract.1.m.key");
        g.provable(
            "SimpleEvoting/simple_evoting.SMT(simple_evoting.SMT__send(simple_evoting.Message,int,simple_evoting.Server)).Non-interference contract.0.m.key");
        g.provable(
            "SimpleEvoting/simple_evoting.SMTEnv(simple_evoting.SMTEnv__send(int,int,int,simple_evoting.Server,int)).Non-interference contract.0.m.key");
        g.provable(
            "SimpleEvoting/simple_evoting.NetworkClient(simple_evoting.NetworkClient__send((B,simple_evoting.Server,int)).Non-interference contract.0.m.key");
        // g.provable(
        // "SimpleEvoting/simple_evoting.Setup(simple_evoting.Setup__publishResult()).Non-interference
        // contract.0.m.key"););
        // g.provable(
        // "SimpleEvoting/simple_evoting.Setup(simple_evoting.Setup__main()).Non-interference
        // contract.0.m.key"););
        g.provable(
            "SimpleEvoting/simple_evoting.Voter(simple_evoting.Voter__onSendBallot(simple_evoting.Server)).Non-interference contract.1.m.key");
        g.provable(
            "SimpleEvoting/simple_evoting.Voter(simple_evoting.Voter__onSendBallot(simple_evoting.Server)).Non-interference contract.0.m.key");
        return c;
    }


    private static String loadFromFile(String name) throws IOException {
        var stream = ProofCollections.class.getResourceAsStream(name);
        Assertions.assertNotNull(stream, "Failed to find " + name);
        return IOUtil.readFrom(stream);
    }

}
