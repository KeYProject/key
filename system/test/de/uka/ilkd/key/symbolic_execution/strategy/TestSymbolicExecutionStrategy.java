// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
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
                          true,
                          ALL_IN_ONE_RUN,
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
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          true);
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
                          true,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
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
                          true,
                          false,
                          true,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          true);
   }
}