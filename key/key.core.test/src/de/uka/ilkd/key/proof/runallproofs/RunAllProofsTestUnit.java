package de.uka.ilkd.key.proof.runallproofs;

import java.io.Serializable;

/**
 * A single unit that will be tested during {@link RunAllProofsTest} run. In
 * case {@link RunAllProofsTest} is configured to run in dedicated-process
 * fallback mode, each {@link RunAllProofsTestUnit} is executed in a separate
 * process.
 * 
 * @author Kai Wallisch
 *
 */
public abstract class RunAllProofsTestUnit implements Serializable {

   /**
    * Data structure for test results consisting of a string message and a
    * boolean value which specifies whether a test run was successful or not.
    */
   public static class TestResult implements Serializable {
      public final String message;
      public final boolean success;

      public TestResult(String message, boolean success) {
         this.message = message;
         this.success = success;
      }
   }

   /**
    * Note: This is only relevant in case {@link RunAllProofsTestUnit}s are
    * configured (in {@link RunAllProofsTest}) to be exexecuted in separate
    * threads each. Test results will be stored in a temporary directory. Each
    * {@link RunAllProofsTestUnit} gets a separate subdirectory in that
    * temporary directory. In case the subdirectory belonging to a specific
    * {@link RunAllProofsTestUnit} shall be easily recognizable, one can specify
    * a prefix for that {@link RunAllProofsTestUnit}. This can be done by
    * overriding this method.
    */
   public String getTempDirectoryPrefix() {
      return null;
   }

   /**
    * Run the test of this unit and return a {@link TestResult}.
    */
   public abstract TestResult runTest() throws Exception;
}
