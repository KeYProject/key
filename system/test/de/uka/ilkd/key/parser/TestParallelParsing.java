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

package de.uka.ilkd.key.parser;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import de.uka.ilkd.key.parser.schemajava.SchemaJavaParser;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * This {@link TestCase} tests the parallel usage of {@link KeYParser}
 * and {@link SchemaJavaParser}.
 * @author Martin Hentschel
 */
public class TestParallelParsing extends AbstractSymbolicExecutionTestCase {
   /**
    * Loads both proof files contained in {@code "examples/_testcase/parser/MultipleRecursion"}
    * in parallel using {@code 4} {@link Thread}s in total.
    * @throws Exception Occurred Exception.
    */
   public void testLoadingOfTwoDifferentProofFiles() throws Exception {
      doParallelTest(keyRepDirectory,
                     2,
                     "examples/_testcase/parser/MultipleRecursion/MultipleRecursion[MultipleRecursion__a()]_JML_normal_behavior_operation_contract_0.proof",
                     "examples/_testcase/parser/MultipleRecursion/MultipleRecursion[MultipleRecursion__b()]_JML_normal_behavior_operation_contract_0.proof");
   }
   
   /**
    * Executes the test steps.
    * @param baseDir The base directory.
    * @param numOfThreadsPerLocation The number of {@link Thread}s per location.
    * @param locations The locations to load.
    * @throws Exception Occurred Exception.
    */
   protected void doParallelTest(File baseDir, 
                                 int numOfThreadsPerLocation,
                                 String... locations) throws Exception {
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try {
         setOneStepSimplificationEnabled(null, true);
         // Create threads
         List<LoadThread> threads = new LinkedList<LoadThread>();
         for (String path : locations) {
            for (int i = 0; i < numOfThreadsPerLocation; i++) {
               final File location = new File(baseDir, path);
               threads.add(new LoadThread(location));
            }
         }
         // Start threads
         for (LoadThread thread : threads) {
            thread.start();
         }
         // Wait for threads
         for (LoadThread thread : threads) {
            while (thread.isAlive()) {
               try {
                  Thread.sleep(500);
               }
               catch (InterruptedException e) {
               }
            }
         }
         // Test results
         for (LoadThread thread : threads) {
            if (thread.getException() != null) {
               throw thread.getException();
            }
         }
      }
      finally {
         // Restore original options
         setOneStepSimplificationEnabled(null, originalOneStepSimplification);
      }
   }
   
   /**
    * Helper {@link Thread} used by {@link TestParallelParsing#doParallelTest(File, int, String...)}
    * to load a location in KeY.
    * @author Martin Hentschel
    */
   private static class LoadThread extends Thread {
      /**
       * The location to load.
       */
      private final File location;
      
      /**
       * Occurred {@link Exception}.
       */
      private Exception exception;
      
      /**
       * Constructor. 
       * @param location The location to load.
       */
      public LoadThread(File location) {
         this.location = location;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void run() {
         try {
            KeYEnvironment<CustomUserInterface> env = KeYEnvironment.load(new JavaProfile(), location, null, null);
            env.dispose();
         }
         catch (Exception e) {
            exception = e;
         }
      }

      /**
       * Returns the occurred {@link Exception}.
       * @return The occurred {@link Exception}.
       */
      public Exception getException() {
         return exception;
      }
   }
}