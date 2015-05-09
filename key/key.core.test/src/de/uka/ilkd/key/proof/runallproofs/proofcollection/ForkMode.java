package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;

/**
 * Enum for different fork modes available for {@link RunAllProofsTest} run. In
 * case anything else than default {@link #NOFORK} is used,
 * {@link RunAllProofsTest} will create subprocesses during test run. Creating
 * subprocesses can be used to ensure that KeY prover is started from a clean
 * state for specific parts of a test run.
 * 
 * @author Kai Wallisch
 */
public enum ForkMode {
   /**
    * Default fork mode, in which {@link RunAllProofsTest} does not create any
    * subprocesses.
    */
   NOFORK("noFork"),
   /**
    * Causes {@link RunAllProofsTest} to create a new subprocess for each group
    * of files. All files from the same group will be proven together in the
    * same subprocess. Files from different groups will be proven in different
    * subprocesses. Actually, since one JUnit test case is created from each
    * group and {@link RunAllProofsTest} is a set of parameterized test cases,
    * this essentially means that each test case from {@link RunAllProofsTest}
    * is executed in a separate thread.
    */
   PERGROUP("perGroup"),
   /**
    * In this mode, a new subprocess will be created for each KeY file that is
    * proven during test run of {@link RunAllProofsTest}.
    */
   PERFILE("perFile");

   /**
    * Name of every fork mode that can be used in
    * {@link ProofCollectionSettings} to activate that specific fork mode.
    * 
    * @see {@link ProofCollectionSettings#getForkMode()}
    */
   public final String settingName;

   ForkMode(String settingName) {
      this.settingName = settingName;
   }

}
