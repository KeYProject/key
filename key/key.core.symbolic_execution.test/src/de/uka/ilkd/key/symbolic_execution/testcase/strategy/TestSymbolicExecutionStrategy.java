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

package de.uka.ilkd.key.symbolic_execution.testcase.strategy;

import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;

/**
 * Tests for {@link SymbolicExecutionStrategy}
 * @author Martin Hentschel
 */
public class TestSymbolicExecutionStrategy extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests example: /set/nonExecutionBranchHidingArraysIndexOf
    */
   public void testNonExecutionBranchHidingArraysIndexOf_hiding_side_proof() throws Exception {
      doSETTestAndDispose(testCaseDirectory, 
                          "/set/nonExecutionBranchHidingArraysIndexOf/test/Arrays.java", 
                          "Arrays", 
                          "indexOf", 
                          "array != null && filter != null && \\invariant_for(filter)",
                          "/set/nonExecutionBranchHidingArraysIndexOf/oracle/Arrays_hiding_side_proof.xml",
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
                          false,
                          false,
                          true);
   }
   /**
    * Tests example: /set/nonExecutionBranchHidingArraysIndexOf
    */
   public void testNonExecutionBranchHidingArraysIndexOf_hiding_off() throws Exception {
      doSETTestAndDispose(testCaseDirectory, 
                          "/set/nonExecutionBranchHidingArraysIndexOf/test/Arrays.java", 
                          "Arrays", 
                          "indexOf", 
                          "array != null && filter != null && \\invariant_for(filter)",
                          "/set/nonExecutionBranchHidingArraysIndexOf/oracle/Arrays_hiding_off.xml",
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
                          false,
                          false,
                          true);
   }
   
   /**
    * Tests example: /set/nonExecutionBranchHidingLoopInvariantWithSplittingQuery
    */
   public void testNonExecutionBranchHidingLoopInvariantWithSplittingQuery_hiding_side_proof() throws Exception {
      doSETTestAndDispose(testCaseDirectory, 
                          "/set/nonExecutionBranchHidingLoopInvariantWithSplittingQuery/test/LoopInvariantWithSplittingQuery.java", 
                          "LoopInvariantWithSplittingQuery", 
                          "main", 
                          null,
                          "/set/nonExecutionBranchHidingLoopInvariantWithSplittingQuery/oracle/LoopInvariantWithSplittingQuery_hiding_side_proof.xml",
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
                          false,
                          false,
                          true);
   }
   
   /**
    * Tests example: /set/nonExecutionBranchHidingLoopInvariantWithSplittingQuery
    */
   public void testNonExecutionBranchHidingLoopInvariantWithSplittingQuery_hiding_off() throws Exception {
      doSETTestAndDispose(testCaseDirectory, 
                          "/set/nonExecutionBranchHidingLoopInvariantWithSplittingQuery/test/LoopInvariantWithSplittingQuery.java", 
                          "LoopInvariantWithSplittingQuery", 
                          "main", 
                          null,
                          "/set/nonExecutionBranchHidingLoopInvariantWithSplittingQuery/oracle/LoopInvariantWithSplittingQuery_hiding_off.xml",
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
                          false,
                          false,
                          true);
   }
   
   /**
    * Tests example: /set/nonExecutionBranchHidingQueryInPrecondition
    */
   public void testNonExecutionBranchHidingQueryInPrecondition_hiding_side_proof() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingQueryInPrecondition/test/QueryInPrecondition.java",
                          "QueryInPrecondition",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingQueryInPrecondition/oracle/QueryInPrecondition_hiding_side_proof.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingQueryInPrecondition
    */
   public void testNonExecutionBranchHidingQueryInPrecondition_hiding_off() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingQueryInPrecondition/test/QueryInPrecondition.java",
                          "QueryInPrecondition",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingQueryInPrecondition/oracle/QueryInPrecondition_hiding_off.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingComplexPrecondition
    */
   public void testNonExecutionBranchHidingComplexPrecondition_hiding_side_proof() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingComplexPrecondition/test/ComplexPrecondition.java",
                          "ComplexPrecondition",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingComplexPrecondition/oracle/ComplexPrecondition_hiding_side_proof.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingComplexPrecondition
    */
   public void testNonExecutionBranchHidingComplexPrecondition_hiding_off() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingComplexPrecondition/test/ComplexPrecondition.java",
                          "ComplexPrecondition",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingComplexPrecondition/oracle/ComplexPrecondition_hiding_off.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingQueryWithSideEffects
    */
   public void testNonExecutionBranchHidingQueryWithSideEffects_hiding_side_proof() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingQueryWithSideEffects/test/QueryWithSideEffects.java",
                          "QueryWithSideEffects",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingQueryWithSideEffects/oracle/QueryWithSideEffects_hiding_side_proof.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingQueryWithSideEffects
    */
   public void testNonExecutionBranchHidingQueryWithSideEffects_hiding_off() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingQueryWithSideEffects/test/QueryWithSideEffects.java",
                          "QueryWithSideEffects",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingQueryWithSideEffects/oracle/QueryWithSideEffects_hiding_off.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingQueryWithFields
    */
   public void testNonExecutionBranchHidingQueryWithFields_hiding_side_proof() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingQueryWithFields/test/QueryWithFields.java",
                          "QueryWithFields",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingQueryWithFields/oracle/QueryWithFields_hiding_side_proof.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingQueryWithFields
    */
   public void testNonExecutionBranchHidingQueryWithFields_hiding_off() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingQueryWithFields/test/QueryWithFields.java",
                          "QueryWithFields",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingQueryWithFields/oracle/QueryWithFields_hiding_off.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingSimpleObjectQuery
    */
   public void testNonExecutionBranchHidingSimpleObjectQuery_hiding_side_proof() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingSimpleObjectQuery/test/SimpleObjectQuery.java",
                          "SimpleObjectQuery",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingSimpleObjectQuery/oracle/SimpleObjectQuery_hiding_side_proof.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingSimpleObjectQuery
    */
   public void testNonExecutionBranchHidingSimpleObjectQuery_hiding_off() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingSimpleObjectQuery/test/SimpleObjectQuery.java",
                          "SimpleObjectQuery",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingSimpleObjectQuery/oracle/SimpleObjectQuery_hiding_off.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingSimpleBooleanQuery
    */
   public void testNonExecutionBranchHidingSimpleBooleanQuery_hiding_side_proof() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingSimpleBooleanQuery/test/SimpleBooleanQuery.java",
                          "SimpleBooleanQuery",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingSimpleBooleanQuery/oracle/SimpleBooleanQuery_hiding_side_proof.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingSimpleBooleanQuery
    */
   public void testNonExecutionBranchHidingSimpleBooleanQuery_hiding_off() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingSimpleBooleanQuery/test/SimpleBooleanQuery.java",
                          "SimpleBooleanQuery",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingSimpleBooleanQuery/oracle/SimpleBooleanQuery_hiding_off.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingSimpleIntQuery
    */
   public void testNonExecutionBranchHidingSimpleIntQuery_mainWithSymbolicUpdates_hiding_side_proof() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingSimpleIntQuery/test/SimpleIntQuery.java",
                          "SimpleIntQuery",
                          "mainWithSymbolicUpdates",
                          null,
                          "/set/nonExecutionBranchHidingSimpleIntQuery/oracle/SimpleIntQuery_mainWithSymbolicUpdates_hiding_side_proof.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingSimpleIntQuery
    */
   public void testNonExecutionBranchHidingSimpleIntQuery_mainWithUpdates_hiding_side_proof() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingSimpleIntQuery/test/SimpleIntQuery.java",
                          "SimpleIntQuery",
                          "mainWithUpdates",
                          null,
                          "/set/nonExecutionBranchHidingSimpleIntQuery/oracle/SimpleIntQuery_mainWithUpdates_hiding_side_proof.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingSimpleIntQuery
    */
   public void testNonExecutionBranchHidingSimpleIntQuery_main_hiding_side_proof() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingSimpleIntQuery/test/SimpleIntQuery.java",
                          "SimpleIntQuery",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingSimpleIntQuery/oracle/SimpleIntQuery_main_hiding_side_proof.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/nonExecutionBranchHidingSimpleIntQuery
    */
   public void testNonExecutionBranchHidingSimpleIntQuery_main_hiding_off() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/nonExecutionBranchHidingSimpleIntQuery/test/SimpleIntQuery.java",
                          "SimpleIntQuery",
                          "main",
                          null,
                          "/set/nonExecutionBranchHidingSimpleIntQuery/oracle/SimpleIntQuery_main_hiding_off.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/aliasTest
    */
   public void testAliasTest_Array_AliasChecksNever() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/aliasTest/test/AliasTest.java",
                          "AliasTest",
                          "array",
                          "w != null && array != null && array.length == 2 && array[0] != null && array[1] != null",
                          "/set/aliasTest/oracle/AliasTest_array_never.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/aliasTest
    */
   public void testAliasTest_Array_AliasChecksImmediately() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/aliasTest/test/AliasTest.java",
                          "AliasTest",
                          "array",
                          "w != null && array != null && array.length == 2 && array[0] != null && array[1] != null",
                          "/set/aliasTest/oracle/AliasTest_array_immediately.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/aliasTest
    */
   public void testAliasTest_Objects_AliasChecksNever() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/aliasTest/test/AliasTest.java",
                          "AliasTest",
                          "main",
                          "a != null && b != null",
                          "/set/aliasTest/oracle/AliasTest_main_never.xml",
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
                          false,
                          false,
                          true);
   }

   /**
    * Tests example: /set/aliasTest
    */
   public void testAliasTest_Objects_AliasChecksImmediately() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                          "/set/aliasTest/test/AliasTest.java",
                          "AliasTest",
                          "main",
                          "a != null && b != null",
                          "/set/aliasTest/oracle/AliasTest_main_immediately.xml",
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
                          false,
                          false,
                          true);
   }
}