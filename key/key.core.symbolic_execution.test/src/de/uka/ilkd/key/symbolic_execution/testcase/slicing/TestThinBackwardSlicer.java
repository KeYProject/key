package de.uka.ilkd.key.symbolic_execution.testcase.slicing;

import java.io.File;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.slicing.ThinBackwardSlicer;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
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

// TODO: Support anonymizing locations
//   /** 
//    * Tests slicing on the example {@code simpleStatiLoopInvariantTest}.
//    * @throws Exception Occurred Exception.
//    */
//   public void testSimpleStatiLoopInvariantTest() throws Exception {
//      doSlicingTest("/slicing/simpleStatiLoopInvariantTest/SimpleStatiLoopInvariantTest.proof", 
//                    new ReturnSelector(224),
//                    true,
//                    12);
//   }

   /**
    * Tests slicing on the example {@code simpleLoopInvariantTest}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLoopInvariantTest() throws Exception {
      doSlicingTest("/slicing/simpleLoopInvariantTest/SimpleLoopInvariantTest.proof", 
                    new ReturnSelector(125),
                    true,
                    9);
   }

   /**
    * Tests slicing on the example {@code arrayIndexAsVariableFieldTest}.
    * @throws Exception Occurred Exception.
    */
   public void testArrayIndexAsVariableFieldTest() throws Exception {
      doSlicingTest("/slicing/arrayIndexAsVariableFieldTest/ArrayIndexAsVariableFieldTest.proof", 
                    new ReturnSelector(412),
                    true,
                    408, 397, 315, 256, 148);
   }

   /**
    * Tests slicing on the example {@code arrayIndexVariableTest}.
    * @throws Exception Occurred Exception.
    */
   public void testArrayIndexVariableTest() throws Exception {
      doSlicingTest("/slicing/arrayIndexVariableTest/ArrayIndexVariableTest.proof", 
                    new ReturnSelector(347),
                    true,
                    343, 332, 258, 211, 118);
   }

   /**
    * Tests slicing on the example {@code arrayIndexSideeffectsBevore}.
    * @throws Exception Occurred Exception.
    */
   public void testArrayIndexSideeffectsBevore() throws Exception {
      doSlicingTest("/slicing/arrayIndexSideeffectsBevore/ArrayIndexSideeffectsBevore.proof", 
                    new ReturnSelector(211),
                    true,
                    148, 55);
   }

   /**
    * Tests slicing on the example {@code arrayIndexSideeffectsAfter}.
    * @throws Exception Occurred Exception.
    */
   public void testArrayIndexSideeffectsAfter() throws Exception {
      doSlicingTest("/slicing/arrayIndexSideeffectsAfter/ArrayIndexSideeffectsAfter.proof", 
                    new ReturnSelector(216),
                    true,
                    163, 59);
   }

   /**
    * Tests slicing on the example {@code simpleMultidimensionArrayTest}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleMultidimensionArrayTest() throws Exception {
      doSlicingTest("/slicing/simpleMultidimensionArrayTest/SimpleMultidimensionArrayTest.proof", 
                    new ReturnSelector(461),
                    true,
                    445, 441, 416, 353, 172, 133);
   }

   /**
    * Tests slicing on the example {@code simpleArrayTest}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleArrayTest() throws Exception {
      doSlicingTest("/slicing/simpleArrayTest/SimpleArrayTest.proof", 
                    new ReturnSelector(202),
                    false,
                    182, 36, 21);
   }

   /**
    * Tests slicing on the example {@code figure2Param}.
    * @throws Exception Occurred Exception.
    */
   public void testFigure2Param_right() throws Exception {
      doSlicingTest("/slicing/figure2Param/Figure2Param.proof", 
                    new RightAssignmentSelector(165),
                    true,
                    151, 85);
   }

   /**
    * Tests slicing on the example {@code figure2Local}.
    * @throws Exception Occurred Exception.
    */
   public void testFigure2Local_right() throws Exception {
      doSlicingTest("/slicing/figure2Local/Figure2Local.proof", 
                    new RightVariableDeclarationSelector(168),
                    true,
                    154, 86);
   }

   /**
    * Tests slicing on the example {@code figure2Instance}.
    * @throws Exception Occurred Exception.
    */
   public void testFigure2Instance_right() throws Exception {
      doSlicingTest("/slicing/figure2Instance/Figure2Instance.proof", 
                    new RightAssignmentSelector(269),
                    true,
                    231, 171, 169, 154, 150, 133, 99);
   }

   /**
    * Tests slicing on the example {@code valueChange}.
    * @throws Exception Occurred Exception.
    */
   public void testValueChange() throws Exception {
      doSlicingTest("/slicing/valueChange/ValueChange.proof", 
                    new ReturnSelector(113),
                    true,
                    109, 97, 81, 77, 52);
   }

   /**
    * Tests slicing on the example {@code readWriteTest}.
    * @throws Exception Occurred Exception.
    */
   public void testReadWriteTest() throws Exception {
      doSlicingTest("/slicing/readWriteTest/ReadWriteTest.proof", 
                    new ReturnSelector(40),
                    true,
                    36, 29, 21, 11);
   }

   /**
    * Tests slicing on the example {@code aliasChanged}.
    * @throws Exception Occurred Exception.
    */
   public void testAliasChanged() throws Exception {
      doSlicingTest("/slicing/aliasChanged/AliasChanged.proof", 
                    new ReturnSelector(225),
                    false,
                    220, 216, 86, 57);
   }

   /**
    * Tests slicing on the example {@code aliasNotAvailable}.
    * @throws Exception Occurred Exception.
    */
   public void testAliasNotAvailable() throws Exception {
      doSlicingTest("/slicing/aliasNotAvailable/AliasNotAvailable.proof", 
                    new ReturnSelector(200),
                    false,
                    195, 191, 107, 86);
   }

   /**
    * Tests slicing on the example {@code intEndTest}.
    * @throws Exception Occurred Exception.
    */
   public void testIntEndTest() throws Exception {
      doSlicingTest("/slicing/intEndTest/IntEndTest.proof", 
                    new ReturnSelector(22),
                    false,
                    18, 16);
   }

   /**
    * Tests slicing on the example {@code simpleAliasChanged}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleAliasChanged() throws Exception {
      doSlicingTest("/slicing/simpleAliasChanged/SimpleAliasChanged.proof", 
                    new ReturnSelector(36),
                    false,
                    24);
   }

   /**
    * Tests slicing on the example {@code instanceFieldsAliased}.
    * @throws Exception Occurred Exception.
    */
   public void testInstanceFieldsAliased() throws Exception {
      doSlicingTest("/slicing/instanceFieldsAliased/InstanceFieldsAliased.proof", 
                    new ReturnSelector(194),
                    false,
                    189, 185, 68);
   }
   
   /**
    * Tests slicing on the example {@code nestedInstanceFields}.
    * @throws Exception Occurred Exception.
    */
   public void testNestedInstanceFields() throws Exception {
      doSlicingTest("/slicing/nestedInstanceFields/NestedInstanceFields.proof", 
                    new ReturnSelector(153),
                    false,
                    148, 144, 41, 27);
   }
   
   /**
    * Tests slicing on the example {@code methodCallTest}.
    * @throws Exception Occurred Exception.
    */
   public void testMethodCallTest() throws Exception {
      doSlicingTest("/slicing/methodCallTest/MethodCallTest.proof", 
                    new ReturnSelector(164),
                    false,
                    111, 39, 15);
   }

   /**
    * Tests slicing on the example {@code aliasing}.
    * @throws Exception Occurred Exception.
    */
   public void testAliasing() throws Exception {
      doSlicingTest("/slicing/aliasing/Aliasing.proof", 
                    new ReturnSelector(62),
                    false,
                    58, 20, 15);
   }
   
   /**
    * Tests slicing on the example {@code nestedInstanceAccess}.
    * @throws Exception Occurred Exception.
    */
   public void testNestedInstanceAccess_subResult() throws Exception {
      doSlicingTest("/slicing/nestedInstanceAccess/NestedInstanceAccess.proof", 
                    new ReturnSelector(138),
                    false,
                    136, 132, 127, 113, 86, 54, 39);
   }

   /**
    * Tests slicing on the example {@code figure2}.
    * @throws Exception Occurred Exception.
    */
   public void testFigure2_right() throws Exception {
      doSlicingTest("/slicing/figure2/Figure2.proof", 
                    new RightAssignmentSelector(271),
                    false,
                    231, 168);
   }

   /**
    * Tests slicing on the example {@code figure2}.
    * @throws Exception Occurred Exception.
    */
   public void testFigure2_left() throws Exception {
      doSlicingTest("/slicing/figure2/Figure2.proof", 
                    new LeftAssignmentSelector(271),
                    false,
                    271, 231, 168);
   }

   /**
    * Tests slicing on the example {@code simpleInstanceFields}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleInstanceFields() throws Exception {
      doSlicingTest("/slicing/simpleInstanceFields/SimpleInstanceFields.proof", 
                    new ReturnSelector(87),
                    false,
                    82, 78, 18, 13);
   }
   
   /**
    * Tests slicing on the example {@code simpleThisInstanceFields}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleThisInstanceFields() throws Exception {
      doSlicingTest("/slicing/simpleThisInstanceFields/SimpleThisInstanceFields.proof", 
                    new ReturnSelector(48),
                    false,
                    46, 42, 11, 9);
   }
   
   /**
    * Tests slicing on the example {@code simpleStaticFields}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleStaticFields() throws Exception {
      doSlicingTest("/slicing/simpleStaticFields/SimpleStaticFields.proof", 
                    new ReturnSelector(63),
                    false,
                    57, 15, 8);
   }
   
   /**
    * Tests slicing on the example {@code simpleLocalVariables}.
    * @throws Exception Occurred Exception.
    */
   public void testSimpleLocalVariables() throws Exception {
      doSlicingTest("/slicing/simpleLocalVariables/SimpleLocalVariables.proof", 
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
      File proofFile = new File(testCaseDirectory, proofFileInRepository);
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
    * {@link ISeedLocationSelector} which searches the right side of a variable declaration.
    * @author Martin Hentschel
    */
   protected static class RightVariableDeclarationSelector implements ISeedLocationSelector {
      /**
       * The serial ID of the seed node.
       */
      private final int seedNodeId;
      
      /**
       * Constructor.
       * @param seedNodeId The serial ID of the seed node.
       */
      public RightVariableDeclarationSelector(int seedNodeId) {
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
         assertTrue(activeStatemt instanceof VariableDeclaration);
         VariableDeclaration variableDeclaration = (VariableDeclaration) activeStatemt;
         SourceElement seedLocation = variableDeclaration.getChildAt(1);
         assertTrue(seedLocation instanceof VariableSpecification);
         return new Pair<Node, ReferencePrefix>(seedNode, (ReferencePrefix) ((VariableSpecification) seedLocation).getInitializer());
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
