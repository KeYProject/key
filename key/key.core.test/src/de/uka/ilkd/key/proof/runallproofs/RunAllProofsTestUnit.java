package de.uka.ilkd.key.proof.runallproofs;

import java.io.Serializable;

/**
 * A single unit that will be tested during {@link RunAllProofsTest} run.
 * 
 * @author Kai Wallisch
 */
public abstract class RunAllProofsTestUnit implements Serializable {

   /**
    * The name of this test.
    */
   public String testName;

   /**
    * Method {@link Object#toString()} is used by class {@link RunAllProofsTest}
    * to determine the name of a test case. It is overridden here so that test
    * cases can be easily recognized by their name.
    */
   @Override
   public String toString() {
      return testName;
   }

   public RunAllProofsTestUnit(String name) {
      this.testName = name;
   }

   /**
    * Run the test of this unit and return a {@link TestResult}.
    */
   public abstract TestResult runTest() throws Exception;
}
