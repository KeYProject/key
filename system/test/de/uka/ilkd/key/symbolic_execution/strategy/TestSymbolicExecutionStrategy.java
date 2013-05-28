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
