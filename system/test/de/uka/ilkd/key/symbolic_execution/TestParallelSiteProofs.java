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

package de.uka.ilkd.key.symbolic_execution;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * This test class makes sure that parallel site proofs are working. It is only
 * verified that no exception is thrown and not that correct results are computed.
 * @author Martin Hentschel
 */
// TODO: Add test case class to test suite "TestKey" after fixing exceptions
public class TestParallelSiteProofs extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests parallel site proofs on a new instantiate proof after applying "resume" on it.
    */
   //Commented out for the moment as Hudson throws an OOM Exception
   public void xxxtestNewProof() throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      // Define test settings
      String javaPathInkeyRepDirectory = "examples/_testcase/set/magic42/test/Magic42.java";
      String containerTypeName = "Magic42";
      final String methodFullName = "compute";
      String oraclePathInBaseDirFile = "examples/_testcase/set/magic42/oracle/Magic42.xml";
      // Create proof environment for symbolic execution
      SymbolicExecutionEnvironment<CustomUserInterface> env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, containerTypeName, methodFullName, null, false, false, false, false, false, false, false);
      try {
         // Resume
         resume(env.getUi(), env.getBuilder(), oraclePathInBaseDirFile, keyRepDirectory);
         // Do test steps
         doParallelSiteProofTest(env);
      }
      finally {
         env.dispose();
      }
   }
   
   /**
    * Tests parallel site proofs on a proof reconstructed from a *.proof file.
    */
   public void testProofFile() throws ProofInputException, IOException, ProblemLoaderException {
      // Define test settings
      String javaPathInkeyRepDirectory = "examples/_testcase/set/magic42/test/Magic42.proof";
      // Create proof environment for symbolic execution
      SymbolicExecutionEnvironment<CustomUserInterface> env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInkeyRepDirectory, false, false, false, false, false, false, false);
      try {
         // Do test steps
         doParallelSiteProofTest(env);
      }
      finally {
         env.dispose();
      }
   }
   
   /**
    * Executes the test steps to make sure that parallel tests are working
    * without thrown {@link Exception}s. 
    * @param env The {@link SymbolicExecutionEnvironment} to use.
    */
   protected void doParallelSiteProofTest(SymbolicExecutionEnvironment<CustomUserInterface> env) {
      // Create threads
      List<SiteProofThread<?>> threads = new LinkedList<SiteProofThread<?>>();
      ExecutionNodePreorderIterator iter = new ExecutionNodePreorderIterator(env.getBuilder().getStartNode());
      while (iter.hasNext() && threads.size() < 30) {
         IExecutionNode next = iter.next(); 
         if (next instanceof IExecutionStateNode) {
            threads.add(new ExecutionVariableSiteProofThread((IExecutionStateNode<?>)next));
         }
         if (next instanceof IExecutionMethodReturn) {
            threads.add(new ExecutionReturnValueSiteProofThread((IExecutionMethodReturn)next));
         }
      }
      // Make sure that the correct number of threads are available
      assertEquals(31, threads.size());
      // Start threads
      for (SiteProofThread<?> thread : threads) {
         thread.start();
      }
      // Wait for threads
      waitForThreads(threads, 20 * 1000);
      // Check result
      for (SiteProofThread<?> thread : threads) {
         // Make sure that no exception is thrown.
         if (thread.getException() != null) {
            thread.getException().printStackTrace();
            fail(thread.getException().getMessage());
         }
         // Make sure that something was computed in site proofs.
         assertNotNull(thread.getResult());
      }
   }
   
   /**
    * Waits until the given {@link Thread}s have terminated.
    * @param threads The {@link Thread}s to wait for.
    */
   public static void waitForThreads(List<SiteProofThread<?>> threads, long timeout) {
      long start = System.currentTimeMillis();
      if (threads != null) {
         for (SiteProofThread<?> thread : threads) {
            while (thread.isAlive()) {
               if (System.currentTimeMillis() > start + timeout) {
                  fail("Timeout during wait for parallel site proofs.");
               }
               try {
                  Thread.sleep(100);
               }
               catch (InterruptedException e) {
                  // Nothing to do.
               }
            }
         }
      }
   }
   
   /**
    * Utility {@link Thread} to execute a parallel site proof.
    * @author Martin Hentschel
    */
   private static abstract class SiteProofThread<T> extends Thread {
      /**
       * A possibly caught exception.
       */
      private Exception exception;
      
      /**
       * The result of the executed site proof.
       */
      private T result;

      /**
       * Returns the caught exception.
       * @return The caught exception.
       */
      public Exception getException() {
         return exception;
      }

      /**
       * Sets the caught exception.
       * @param exception The caught exception.
       */
      protected void setException(Exception exception) {
         this.exception = exception;
      }

      /**
       * Returns the result of the site proof.
       * @return The site proof result.
       */
      public T getResult() {
         return result;
      }

      /**
       * Sets the result of the site proof.
       * @param result The site proof result.
       */
      protected void setResult(T result) {
         this.result = result;
      }
   }
   
   /**
    * A {@link Thread} which computes the variables of a given {@link IExecutionStateNode}
    * via site proofs.
    * @author Martin Hentschel
    */
   private static class ExecutionVariableSiteProofThread extends SiteProofThread<IExecutionVariable[]> {
      /**
       * The {@link IExecutionStateNode} to read variables from.
       */
      private IExecutionStateNode<?> stateNode;

      /**
       * Constructor. 
       * @param stateNode The {@link IExecutionStateNode} to read variables from.
       */
      public ExecutionVariableSiteProofThread(IExecutionStateNode<?> stateNode) {
         this.stateNode = stateNode;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void run() {
         try {
            setResult(stateNode.getVariables());
         }
         catch (Exception e) {
            setException(e);
         }
      }
   }
   
   /**
    * A {@link Thread} which computes the method return value of a given 
    * {@link IExecutionMethodReturn} via a site proof.
    * @author Martin Hentschel
    */
   private static class ExecutionReturnValueSiteProofThread extends SiteProofThread<String> {
      /**
       * The {@link IExecutionMethodReturn} to read method return value from.
       */
      private IExecutionMethodReturn returnNode;

      /**
       * Constructor
       * @param returnNode The {@link IExecutionMethodReturn} to read method return value from.
       */
      public ExecutionReturnValueSiteProofThread(IExecutionMethodReturn returnNode) {
         this.returnNode = returnNode;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void run() {
         try {
            setResult(returnNode.getNameIncludingReturnValue());
         }
         catch (Exception e) {
            setException(e);
         }
      }
   }
}