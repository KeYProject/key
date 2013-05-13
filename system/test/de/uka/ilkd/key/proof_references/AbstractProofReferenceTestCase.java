package de.uka.ilkd.key.proof_references;

import java.io.File;
import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof_references.analyst.IProofReferencesAnalyst;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Provides the basic functionality to test the proof reference API.
 * @author Martin Hentschel
 */
public abstract class AbstractProofReferenceTestCase extends AbstractSymbolicExecutionTestCase {
   /**
    * Executes the test steps of test methods. 
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param containerTypeName The name of the type which contains the method.
    * @param methodFullName The method name to search.
    * @param useContracts Use contracts or inline method bodies instead.
    * @param analyst The {@link IProofReferencesAnalyst} to use.
    * @param expectedReferences The expected proof references.
    * @throws Exception Occurred Exception.
    */
   protected void doReferenceTest(File baseDir, 
                                  String javaPathInBaseDir, 
                                  String containerTypeName, 
                                  String methodFullName,
                                  boolean useContracts,
                                  final IProofReferencesAnalyst analyst,
                                  final ExpectedProofReferences... expectedReferences) throws Exception {
      IProofTester tester = new IProofTester() {
         @Override
         public void doTest(KeYEnvironment<CustomConsoleUserInterface> environment, Proof proof) throws Exception {
            // Compute proof references
            ImmutableList<IProofReferencesAnalyst> analysts = ImmutableSLList.nil();
            if (analyst != null) {
               analysts = analysts.append(analyst);
            }
            ImmutableList<IProofReference<?>> references = ProofReferenceUtil.computeProofReferences(proof, analysts);
            // Assert proof references
            assertReferences(references, expectedReferences);
         }
      };
      doProofTest(baseDir, javaPathInBaseDir, containerTypeName, methodFullName, useContracts, tester);
   }
   
   /**
    * Extracts all {@link IProofReference}s of the given once which are extracted from the given {@link Node}.
    * @param references The {@link IProofReference}s to search in.
    * @param node The {@link Node} to look for.
    * @return The contained {@link IProofReference}s with the given node.
    */
   protected ImmutableList<IProofReference<?>> findReferences(ImmutableList<IProofReference<?>> references, Node node) {
      ImmutableList<IProofReference<?>> result = ImmutableSLList.nil();
      for (IProofReference<?> reference : references) {
         if (reference.getNode() == node) {
            result = result.append(reference);
         }
      }
      return result;
   }

   /**
    * Tests the given {@link IProofReference}s.
    * @param expected The expected {@link IProofReference}s.
    * @param current The current {@link IProofReference}s.
    */
   protected void assertReferences(ImmutableList<IProofReference<?>> expected, ImmutableList<IProofReference<?>> current) {
      assertNotNull(current);
      assertNotNull(expected);
      assertEquals(current.size(), expected.size());
      Iterator<IProofReference<?>> expectedIter = expected.iterator();
      Iterator<IProofReference<?>> currentIter = current.iterator();
      while (expectedIter.hasNext() && currentIter.hasNext()) {
         IProofReference<?> expectedReference = expectedIter.next();
         IProofReference<?> currentReference = currentIter.next();
         assertEquals(expectedReference.getKind(), currentReference.getKind());
         assertEquals(expectedReference.getTarget(), currentReference.getTarget());
         assertEquals(expectedReference.getNode(), currentReference.getNode());
      }
      assertFalse(expectedIter.hasNext());
      assertFalse(currentIter.hasNext());
   }

   /**
    * Tests the given {@link IProofReference}s.
    * @param current The current {@link IProofReference}s.
    * @param expected The expected {@link ExpectedProofReferences}s.
    */
   protected void assertReferences(ImmutableList<IProofReference<?>> current, ExpectedProofReferences... expected) {
      assertNotNull(current);
      assertNotNull(expected);
      assertEquals(expected.length, current.size());
      int i = 0;
      for (IProofReference<?> currentReference : current) {
         ExpectedProofReferences expectedReference = expected[i];
         assertEquals(expectedReference.getKind(), currentReference.getKind());
         if (expectedReference.getTarget() != null) {
            assertNotNull(currentReference.getTarget());
            assertEquals(expectedReference.getTarget(), currentReference.getTarget().toString());
         }
         else {
            assertNull(currentReference.getTarget());
         }
         i++;
      }
   }
   
   /**
    * Defines the values of an expected proof reference.
    * @author Martin Hentschel
    */
   protected static class ExpectedProofReferences {
      /**
       * The expected kind.
       */
      private String kind;
      
      /**
       * The expected target.
       */
      private String target;

      /**
       * Constructor.
       * @param kind The expected kind.
       * @param target The expected target.
       */
      public ExpectedProofReferences(String kind, String target) {
         this.kind = kind;
         this.target = target;
      }

      /**
       * Returns the expected kind.
       * @return The expected kind.
       */
      public String getKind() {
         return kind;
      }

      /**
       * Returns the expected target.
       * @return The expected target.
       */
      public String getTarget() {
         return target;
      }
   }
   
   /**
    * Does some test steps with a {@link Proof}.
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param containerTypeName The name of the type which contains the method.
    * @param methodFullName The method name to search.
    * @param useContracts Use contracts or inline method bodies instead.
    * @param tester The {@link IProofTester} which executes the test steps.
    * @throws Exception Occurred Exception.
    */
   protected void doProofTest(File baseDir, 
                              String javaPathInBaseDir, 
                              String containerTypeName, 
                              String methodFullName,
                              boolean useContracts,
                              IProofTester tester) throws Exception {
      assertNotNull(tester);
      // Make sure that required files exists
      File javaFile = new File(baseDir, javaPathInBaseDir);
      assertTrue(javaFile.exists());
      // Load java file
      KeYEnvironment<CustomConsoleUserInterface> environment = KeYEnvironment.load(javaFile, null, null);
      Proof proof = null;
      try {
         // Search method to proof
         IProgramMethod pm = searchProgramMethod(environment.getServices(), containerTypeName, methodFullName);
         // Find first contract.
         ImmutableSet<FunctionalOperationContract> operationContracts = environment.getSpecificationRepository().getOperationContracts(pm.getContainerType(), pm);
         assertFalse(operationContracts.isEmpty());
         FunctionalOperationContract foc = operationContracts.iterator().next();
         // Start proof
         proof = environment.createProof(foc.createProofObl(environment.getInitConfig(), foc));
         assertNotNull(proof);
         // Start auto mode
         StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
         sp.put(StrategyProperties.METHOD_OPTIONS_KEY, useContracts ? StrategyProperties.METHOD_CONTRACT : StrategyProperties.METHOD_EXPAND);
         proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
         environment.getUi().startAndWaitForAutoMode(proof);
         // Do test
         tester.doTest(environment, proof);
      }
      finally {
         if (proof != null) {
            proof.dispose();
         }
         environment.dispose();
      }
   }
   
   /**
    * Executes some proof steps with on given {@link Proof}. 
    * @author Martin Hentschel
    */
   protected static interface IProofTester {
      /**
       * Execute the test.
       * @param environment The {@link KeYEnvironment} to test.
       * @param proof The {@link Proof} to test.
       * @throws Exception Occurred Exception.
       */
      public void doTest(KeYEnvironment<CustomConsoleUserInterface> environment, Proof proof) throws Exception;
   }
}
