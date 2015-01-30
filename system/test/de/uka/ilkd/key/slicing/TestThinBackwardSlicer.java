package de.uka.ilkd.key.slicing;

import java.io.File;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

/**
 * Tests for {@link ThinBackwardSlicer}.
 * @author Martin Hentschel
 */
public class TestThinBackwardSlicer extends AbstractSymbolicExecutionTestCase {
   /**
    * Flag to print found slices in the console.
    */
   public static final boolean PRINT_SLICE = false;
   
   /**
    * Tests slicing on the example {@code simpleLocalVariables}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLocalVariables() throws Exception {
      doSlicingTest("examples/_testcase/slicing/simpleLocalVariables/SimpleLocalVariables.proof", 
                    24,
                    20, 11, 7);
   }
   
   /**
    * Performs a slicing test.
    * @param proofFileInRepository The path to the proof file.
    * @param seedNodeId The serial ID of the seed node.
    * @param expectedSlice The serial IDs of the expected slices.
    * @throws Exception Occurred Exception
    */
   protected void doSlicingTest(String proofFileInRepository,
                                int seedNodeId,
                                int... expectedSlice) throws Exception {
      // Load proof
      File proofFile = new File(keyRepDirectory, proofFileInRepository);
      assertTrue(proofFile.exists());
      KeYEnvironment<?> environment = KeYEnvironment.load(proofFile, null, null);
      try {
         // Get loaded proof
         Proof proof = environment.getLoadedProof();
         assertNotNull(proof);
         // Find seed
         Node seedNode = findNode(proof, seedNodeId);
         assertNotNull(seedNode);
         // Get seed location
         SourceElement activeStatemt = seedNode.getNodeInfo().getActiveStatement();
         assertTrue(activeStatemt instanceof Return);
         Return returnStatement = (Return) activeStatemt;
         Expression seedLocation = returnStatement.getExpression();
         // Perform slicing
         ThinBackwardSlicer slicer = new ThinBackwardSlicer();
         ImmutableArray<Node> slices = slicer.slice(seedNode, seedLocation);
         // Print slice if requested
         if (PRINT_SLICE) {
            System.out.println("Found Slices: " + slices.size());
            for (Node slice : slices) {
               System.out.println(slice.serialNr());
            }
         }
         // Compare slice
         assertEquals(expectedSlice.length, slices.size());
         for (int i = 0; i < expectedSlice.length; i++) {
            Node slice = slices.get(i);
            assertNotNull(slice);
            assertEquals(expectedSlice[i], slice.serialNr());
         }
      }
      finally {
         environment.dispose();
      }
   }

   /**
    * Searches a {@link Node} with the given serial ID.
    * @param proof The {@link Proof} to search in.
    * @param nodeId The ID of the {@link Node} to search.
    * @return The found {@link Node} or {@code null} if not available.
    */
   protected Node findNode(Proof proof, int nodeId) {
      FindNodeProofVisitor visitor = new FindNodeProofVisitor(nodeId);
      proof.breadthFirstSearch(proof.root(), visitor);
      return visitor.getNode();
   }
   
   /**
    * Utility class used by {@link TestThinBackwardSlicer#findNode(Proof, int)}.
    * @author Martin Hentschel
    */
   private static class FindNodeProofVisitor implements ProofVisitor {
      /**
       * The ID of the node to search.
       */
      private final int nodeId;

      /**
       * The found node.
       */
      private Node node;
      
      /**
       * Constructor.
       * @param nodeId The ID of the node to search.
       */
      public FindNodeProofVisitor(int nodeId) {
         this.nodeId = nodeId;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void visit(Proof proof, Node visitedNode) {
         if (visitedNode.serialNr() == nodeId) {
            node = visitedNode;
         }
      }

      /**
       * Returns the found {@link Node}.
       * @return The found {@link Node} or {@code null} if not available.
       */
      public Node getNode() {
         return node;
      }
   }
}
