package de.uka.ilkd.key.slicing;

import java.io.File;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.symbolic_execution.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.util.Pair;

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
    * Tests slicing on the example {@code intEndTest}.
    * @throws Exception Occurred Exception.
    */
   public void testIntEndTest() throws Exception {
      doSlicingTest("examples/_testcase/slicing/intEndTest/IntEndTest.proof", 
                    new ReturnSelector(22),
                    false,
                    18, 16);
   }

   /**
    * Tests slicing on the example {@code simpleAliasChanged}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleAliasChanged() throws Exception {
      doSlicingTest("examples/_testcase/slicing/simpleAliasChanged/SimpleAliasChanged.proof", 
                    new ReturnSelector(36),
                    false,
                    24);
   }

   /**
    * Tests slicing on the example {@code instanceFieldsAliased}.
    * @throws Exception Occurred Exception.
    */
   public void testInstanceFieldsAliased() throws Exception {
      doSlicingTest("examples/_testcase/slicing/instanceFieldsAliased/InstanceFieldsAliased.proof", 
                    new ReturnSelector(194),
                    false,
                    189, 185, 68);
   }
   
   /**
    * Tests slicing on the example {@code nestedInstanceFields}.
    * @throws Exception Occurred Exception.
    */
   public void testNestedInstanceFields() throws Exception {
      doSlicingTest("examples/_testcase/slicing/nestedInstanceFields/NestedInstanceFields.proof", 
                    new ReturnSelector(153),
                    false,
                    148, 144, 41, 27);
   }
   
   /**
    * Tests slicing on the example {@code methodCallTest}.
    * @throws Exception Occurred Exception.
    */
   public void testMethodCallTest() throws Exception {
      doSlicingTest("examples/_testcase/slicing/methodCallTest/MethodCallTest.proof", 
                    new ReturnSelector(164),
                    false,
                    111, 39, 15);
   }

   /**
    * Tests slicing on the example {@code aliasing}.
    * @throws Exception Occurred Exception.
    */
   public void testAliasing() throws Exception {
      doSlicingTest("examples/_testcase/slicing/aliasing/Aliasing.proof", 
                    new ReturnSelector(62),
                    false,
                    58, 20, 15);
   }
   
   /**
    * Tests slicing on the example {@code nestedInstanceAccess}.
    * @throws Exception Occurred Exception.
    */
   public void testNestedInstanceAccess_subResult() throws Exception {
      doSlicingTest("examples/_testcase/slicing/nestedInstanceAccess/NestedInstanceAccess.proof", 
                    new ReturnSelector(138),
                    false,
                    136, 132, 127, 113, 86, 54, 39);
   }

   /**
    * Tests slicing on the example {@code figure2}.
    * @throws Exception Occurred Exception.
    */
   public void testFigure2_right() throws Exception {
      doSlicingTest("examples/_testcase/slicing/figure2/Figure2.proof", 
                    new RightAssignmentSelector(271),
                    false,
                    231, 168);
   }

   /**
    * Tests slicing on the example {@code figure2}.
    * @throws Exception Occurred Exception.
    */
   public void testFigure2_left() throws Exception {
      doSlicingTest("examples/_testcase/slicing/figure2/Figure2.proof", 
                    new LeftAssignmentSelector(271),
                    false,
                    271, 231, 168);
   }

   /**
    * Tests slicing on the example {@code simpleInstanceFields}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleInstanceFields() throws Exception {
      doSlicingTest("examples/_testcase/slicing/simpleInstanceFields/SimpleInstanceFields.proof", 
                    new ReturnSelector(87),
                    false,
                    82, 78, 18, 13);
   }
   
   /**
    * Tests slicing on the example {@code simpleThisInstanceFields}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleThisInstanceFields() throws Exception {
      doSlicingTest("examples/_testcase/slicing/simpleThisInstanceFields/SimpleThisInstanceFields.proof", 
                    new ReturnSelector(48),
                    false,
                    46, 42, 11, 9);
   }
   
   /**
    * Tests slicing on the example {@code simpleStaticFields}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleStaticFields() throws Exception {
      doSlicingTest("examples/_testcase/slicing/simpleStaticFields/SimpleStaticFields.proof", 
                    new ReturnSelector(63),
                    false,
                    57, 15, 8);
   }
   
   /**
    * Tests slicing on the example {@code simpleLocalVariables}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLocalVariables() throws Exception {
      doSlicingTest("examples/_testcase/slicing/simpleLocalVariables/SimpleLocalVariables.proof", 
                    new ReturnSelector(24),
                    true,
                    20, 11, 7);
   }
   
   /**
    * Performs a slicing test.
    * @param proofFileInRepository The path to the proof file.
    * @param selector The {@link ISeedLocationSelector} to use.
    * @param fullSlize {@code true} if the he full slice is given as expected slice and {@code false} if only a part of the slice is given as expected slice.
    * @param expectedSlice The serial IDs of the expected slices.
    * @throws Exception Occurred Exception
    */
   protected void doSlicingTest(String proofFileInRepository,
                                ISeedLocationSelector selector,
                                boolean fullSlize,
                                int... expectedSlice) throws Exception {
      // Load proof
      File proofFile = new File(keyRepDirectory, proofFileInRepository);
      assertTrue(proofFile.exists());
      KeYEnvironment<?> environment = KeYEnvironment.load(SymbolicExecutionJavaProfile.getDefaultInstance(), proofFile, null, null, true);
      try {
         // Get loaded proof
         Proof proof = environment.getLoadedProof();
         assertNotNull(proof);
         // Find seed
         Pair<Node, ReferencePrefix> seed = selector.findSeed(proof);
         // Perform slicing
         ThinBackwardSlicer slicer = new ThinBackwardSlicer();
         ImmutableArray<Node> slices = slicer.slice(seed.first, seed.second);
         // Print slice if requested
         if (PRINT_SLICE) {
            System.out.println("Found Slices: " + slices.size());
            for (Node slice : slices) {
               System.out.println(slice.serialNr());
            }
         }
         if (fullSlize) {
            // Compare all Nodes in the slice
            assertEquals(expectedSlice.length, slices.size());
            for (int i = 0; i < expectedSlice.length; i++) {
               Node slice = slices.get(i);
               assertNotNull(slice);
               assertEquals(expectedSlice[i], slice.serialNr());
            }
         }
         else {
            // Ensure that only given Nodes exist in the slice maintaining the order
            int currentIndex = 0;
            for (int expected : expectedSlice) {
               Node slice = null;
               while (slice == null && currentIndex < slices.size()) {
                  Node toCheck = slices.get(currentIndex);
                  assertNotNull(toCheck);
                  if (toCheck.serialNr() == expected) {
                     slice = toCheck;
                  }
                  currentIndex++;
               }
               assertNotNull(slice);
            }
         }
      }
      finally {
         environment.dispose();
      }
   }
   
   /**
    * {@link ISeedLocationSelector} which searches the right side of an assignment.
    * @author Martin Hentschel
    */
   protected static class RightAssignmentSelector implements ISeedLocationSelector {
      /**
       * The serial ID of the seed node.
       */
      private final int seedNodeId;
      
      /**
       * Constructor.
       * @param seedNodeId The serial ID of the seed node.
       */
      public RightAssignmentSelector(int seedNodeId) {
         this.seedNodeId = seedNodeId;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Pair<Node, ReferencePrefix> findSeed(Proof proof) {
         // Find seed
         Node seedNode = findNode(proof, seedNodeId);
         assertNotNull(seedNode);
         // Get seed location
         SourceElement activeStatemt = seedNode.getNodeInfo().getActiveStatement();
         assertTrue(activeStatemt instanceof CopyAssignment);
         CopyAssignment assignment = (CopyAssignment) activeStatemt;
         SourceElement seedLocation = assignment.getChildAt(1);
         return new Pair<Node, ReferencePrefix>(seedNode, (ReferencePrefix) seedLocation);
      }
   }
   
   /**
    * {@link ISeedLocationSelector} which searches the left side of an assignment.
    * @author Martin Hentschel
    */
   protected static class LeftAssignmentSelector implements ISeedLocationSelector {
      /**
       * The serial ID of the seed node.
       */
      private final int seedNodeId;
      
      /**
       * Constructor.
       * @param seedNodeId The serial ID of the seed node.
       */
      public LeftAssignmentSelector(int seedNodeId) {
         this.seedNodeId = seedNodeId;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Pair<Node, ReferencePrefix> findSeed(Proof proof) {
         // Find seed
         Node seedNode = findNode(proof, seedNodeId);
         assertNotNull(seedNode);
         // Get seed location
         SourceElement activeStatemt = seedNode.getNodeInfo().getActiveStatement();
         assertTrue(activeStatemt instanceof CopyAssignment);
         CopyAssignment assignment = (CopyAssignment) activeStatemt;
         SourceElement seedLocation = assignment.getChildAt(0);
         return new Pair<Node, ReferencePrefix>(seedNode, (ReferencePrefix) seedLocation);
      }
   }
   
   /**
    * {@link ISeedLocationSelector} which searches a return expression as seed.
    * @author Martin Hentschel
    */
   protected static class ReturnSelector implements ISeedLocationSelector {
      /**
       * The serial ID of the seed node.
       */
      private final int seedNodeId;
      
      /**
       * Constructor.
       * @param seedNodeId The serial ID of the seed node.
       */
      public ReturnSelector(int seedNodeId) {
         this.seedNodeId = seedNodeId;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Pair<Node, ReferencePrefix> findSeed(Proof proof) {
         // Find seed
         Node seedNode = findNode(proof, seedNodeId);
         assertNotNull(seedNode);
         // Get seed location
         SourceElement activeStatemt = seedNode.getNodeInfo().getActiveStatement();
         assertTrue(activeStatemt instanceof Return);
         Return returnStatement = (Return) activeStatemt;
         SourceElement seedLocation = returnStatement.getExpression();
         return new Pair<Node, ReferencePrefix>(seedNode, (ReferencePrefix) seedLocation);
      }
   }
   
   /**
    * Implementations of this interface are used to find the seed.
    * @author Martin Hentschel
    */
   protected static interface ISeedLocationSelector {
      public Pair<Node, ReferencePrefix> findSeed(Proof proof);
   }

   /**
    * Searches a {@link Node} with the given serial ID.
    * @param proof The {@link Proof} to search in.
    * @param nodeId The ID of the {@link Node} to search.
    * @return The found {@link Node} or {@code null} if not available.
    */
   protected static Node findNode(Proof proof, int nodeId) {
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
