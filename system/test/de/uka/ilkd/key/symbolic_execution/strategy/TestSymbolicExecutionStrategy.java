// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;

/**
 * Tests for {@link SymbolicExecutionStrategy}
 * @author Martin Hentschel
 */
public class TestSymbolicExecutionStrategy extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingArraysIndexOf
    */
   public void testNonExecutionBranchHidingArraysIndexOf_hiding_side_proof() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/nonExecutionBranchHidingArraysIndexOf/test/Arrays.java", 
                          "Arrays", 
                          "indexOf", 
                          "array != null && filter != null && \\invariant_for(filter)",
                          "examples/_testcase/set/nonExecutionBranchHidingArraysIndexOf/oracle/Arrays_hiding_side_proof.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          true,
                          false,
                          false,
                          false);
   }
   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingArraysIndexOf
    */
   public void testNonExecutionBranchHidingArraysIndexOf_hiding_off() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/nonExecutionBranchHidingArraysIndexOf/test/Arrays.java", 
                          "Arrays", 
                          "indexOf", 
                          "array != null && filter != null && \\invariant_for(filter)",
                          "examples/_testcase/set/nonExecutionBranchHidingArraysIndexOf/oracle/Arrays_hiding_off.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingLoopInvariantWithSplittingQuery
    */
   public void testNonExecutionBranchHidingLoopInvariantWithSplittingQuery_hiding_side_proof() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/nonExecutionBranchHidingLoopInvariantWithSplittingQuery/test/LoopInvariantWithSplittingQuery.java", 
                          "LoopInvariantWithSplittingQuery", 
                          "main", 
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingLoopInvariantWithSplittingQuery/oracle/LoopInvariantWithSplittingQuery_hiding_side_proof.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          true,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingLoopInvariantWithSplittingQuery
    */
   public void testNonExecutionBranchHidingLoopInvariantWithSplittingQuery_hiding_off() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/nonExecutionBranchHidingLoopInvariantWithSplittingQuery/test/LoopInvariantWithSplittingQuery.java", 
                          "LoopInvariantWithSplittingQuery", 
                          "main", 
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingLoopInvariantWithSplittingQuery/oracle/LoopInvariantWithSplittingQuery_hiding_off.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingQueryInPrecondition
    */
   public void testNonExecutionBranchHidingQueryInPrecondition_hiding_side_proof() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingQueryInPrecondition/test/QueryInPrecondition.java",
                          "QueryInPrecondition",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingQueryInPrecondition/oracle/QueryInPrecondition_hiding_side_proof.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          true,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingQueryInPrecondition
    */
   public void testNonExecutionBranchHidingQueryInPrecondition_hiding_off() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingQueryInPrecondition/test/QueryInPrecondition.java",
                          "QueryInPrecondition",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingQueryInPrecondition/oracle/QueryInPrecondition_hiding_off.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          false,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingComplexPrecondition
    */
   public void testNonExecutionBranchHidingComplexPrecondition_hiding_side_proof() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingComplexPrecondition/test/ComplexPrecondition.java",
                          "ComplexPrecondition",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingComplexPrecondition/oracle/ComplexPrecondition_hiding_side_proof.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          true,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingComplexPrecondition
    */
   public void testNonExecutionBranchHidingComplexPrecondition_hiding_off() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingComplexPrecondition/test/ComplexPrecondition.java",
                          "ComplexPrecondition",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingComplexPrecondition/oracle/ComplexPrecondition_hiding_off.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          false,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingQueryWithSideEffects
    */
   public void testNonExecutionBranchHidingQueryWithSideEffects_hiding_side_proof() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingQueryWithSideEffects/test/QueryWithSideEffects.java",
                          "QueryWithSideEffects",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingQueryWithSideEffects/oracle/QueryWithSideEffects_hiding_side_proof.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          true,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingQueryWithSideEffects
    */
   public void testNonExecutionBranchHidingQueryWithSideEffects_hiding_off() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingQueryWithSideEffects/test/QueryWithSideEffects.java",
                          "QueryWithSideEffects",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingQueryWithSideEffects/oracle/QueryWithSideEffects_hiding_off.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          false,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingQueryWithFields
    */
   public void testNonExecutionBranchHidingQueryWithFields_hiding_side_proof() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingQueryWithFields/test/QueryWithFields.java",
                          "QueryWithFields",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingQueryWithFields/oracle/QueryWithFields_hiding_side_proof.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          true,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingQueryWithFields
    */
   public void testNonExecutionBranchHidingQueryWithFields_hiding_off() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingQueryWithFields/test/QueryWithFields.java",
                          "QueryWithFields",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingQueryWithFields/oracle/QueryWithFields_hiding_off.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          false,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingSimpleObjectQuery
    */
   public void testNonExecutionBranchHidingSimpleObjectQuery_hiding_side_proof() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleObjectQuery/test/SimpleObjectQuery.java",
                          "SimpleObjectQuery",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleObjectQuery/oracle/SimpleObjectQuery_hiding_side_proof.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          true,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingSimpleObjectQuery
    */
   public void testNonExecutionBranchHidingSimpleObjectQuery_hiding_off() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleObjectQuery/test/SimpleObjectQuery.java",
                          "SimpleObjectQuery",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleObjectQuery/oracle/SimpleObjectQuery_hiding_off.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          false,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingSimpleBooleanQuery
    */
   public void testNonExecutionBranchHidingSimpleBooleanQuery_hiding_side_proof() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleBooleanQuery/test/SimpleBooleanQuery.java",
                          "SimpleBooleanQuery",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleBooleanQuery/oracle/SimpleBooleanQuery_hiding_side_proof.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          true,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingSimpleBooleanQuery
    */
   public void testNonExecutionBranchHidingSimpleBooleanQuery_hiding_off() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleBooleanQuery/test/SimpleBooleanQuery.java",
                          "SimpleBooleanQuery",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleBooleanQuery/oracle/SimpleBooleanQuery_hiding_off.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          false,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingSimpleIntQuery
    */
   public void testNonExecutionBranchHidingSimpleIntQuery_mainWithSymbolicUpdates_hiding_side_proof() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleIntQuery/test/SimpleIntQuery.java",
                          "SimpleIntQuery",
                          "mainWithSymbolicUpdates",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleIntQuery/oracle/SimpleIntQuery_mainWithSymbolicUpdates_hiding_side_proof.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          true,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingSimpleIntQuery
    */
   public void testNonExecutionBranchHidingSimpleIntQuery_mainWithUpdates_hiding_side_proof() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleIntQuery/test/SimpleIntQuery.java",
                          "SimpleIntQuery",
                          "mainWithUpdates",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleIntQuery/oracle/SimpleIntQuery_mainWithUpdates_hiding_side_proof.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          true,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingSimpleIntQuery
    */
   public void testNonExecutionBranchHidingSimpleIntQuery_main_hiding_side_proof() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleIntQuery/test/SimpleIntQuery.java",
                          "SimpleIntQuery",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleIntQuery/oracle/SimpleIntQuery_main_hiding_side_proof.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          true,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/nonExecutionBranchHidingSimpleIntQuery
    */
   public void testNonExecutionBranchHidingSimpleIntQuery_main_hiding_off() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleIntQuery/test/SimpleIntQuery.java",
                          "SimpleIntQuery",
                          "main",
                          null,
                          "examples/_testcase/set/nonExecutionBranchHidingSimpleIntQuery/oracle/SimpleIntQuery_main_hiding_off.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          true,
                          true,
                          false,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/aliasTest
    */
   public void testAliasTest_Array_AliasChecksNever() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/aliasTest/test/AliasTest.java",
                          "AliasTest",
                          "array",
                          "w != null && array != null && array.length == 2 && array[0] != null && array[1] != null",
                          "examples/_testcase/set/aliasTest/oracle/AliasTest_array_never.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/aliasTest
    */
   public void testAliasTest_Array_AliasChecksImmediately() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/aliasTest/test/AliasTest.java",
                          "AliasTest",
                          "array",
                          "w != null && array != null && array.length == 2 && array[0] != null && array[1] != null",
                          "examples/_testcase/set/aliasTest/oracle/AliasTest_array_immediately.xml",
                          false,
                          false,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          true,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/aliasTest
    */
   public void testAliasTest_Objects_AliasChecksNever() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/aliasTest/test/AliasTest.java",
                          "AliasTest",
                          "main",
                          "a != null && b != null",
                          "examples/_testcase/set/aliasTest/oracle/AliasTest_main_never.xml",
                          false,
                          true,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }

   /**
    * Tests example: examples/_testcase/set/aliasTest
    */
   public void testAliasTest_Objects_AliasChecksImmediately() throws Exception {
      doSETTestAndDispose(keyRepDirectory,
                          "examples/_testcase/set/aliasTest/test/AliasTest.java",
                          "AliasTest",
                          "main",
                          "a != null && b != null",
                          "examples/_testcase/set/aliasTest/oracle/AliasTest_main_immediately.xml",
                          false,
                          true,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          true,
                          false,
                          false);
   }
}