/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase.slicing;

import java.io.File;

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
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeSymbolicLayoutExtractor;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.impl.AbstractExecutionNode;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.slicing.ThinBackwardSlicer;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.Pair;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.MethodOrderer;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestMethodOrder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * Tests for {@link ThinBackwardSlicer}.
 *
 * @author Martin Hentschel
 */
@TestMethodOrder(MethodOrderer.MethodName.class)
public class TestThinBackwardSlicer extends AbstractSymbolicExecutionTestCase {
    /**
     * Flag to print found slices in the console.
     */
    public static final boolean PRINT_SLICE = false;
    private static final Logger LOGGER = LoggerFactory.getLogger(TestThinBackwardSlicer.class);

    /**
     * Tests slicing on the example {@code blockContractAssignableLocationNotRequested}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testBlockContractAssignableLocationNotRequested() throws Exception {
        doSlicingTest(
            "/slicing/blockContractAssignableLocationNotRequested/BlockContractAssignableLocationNotRequested.proof",
            new ReturnSelector(122), true, 109, 14, 12);
    }

    /**
     * Tests slicing on the example {@code blockContractAssignableRequestedLocation}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testBlockContractAssignableRequestedLocation() throws Exception {
        doSlicingTest(
            "/slicing/blockContractAssignableRequestedLocation/BlockContractAssignableRequestedLocation.proof",
            new ReturnSelector(111), true, 23);
    }

    /**
     * Tests slicing on the example {@code blockContractAssignableEverything}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testBlockContractAssignableEverything() throws Exception {
        doSlicingTest(
            "/slicing/blockContractAssignableEverything/BlockContractAssignableEverything.proof",
            new ReturnSelector(97), true, 23);
    }

    /**
     * Tests slicing on the example {@code methodContractAssignableLocationNotRequested}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testMethodContractAssignableLocationNotRequested() throws Exception {
        doSlicingTest(
            "/slicing/methodContractAssignableLocationNotRequested/MethodContractAssignableLocationNotRequested.proof",
            new ReturnSelector(29), true, 14, 12);
    }

    /**
     * Tests slicing on the example {@code methodContractAssignableRequestedLocation}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testMethodContractAssignableRequestedLocation() throws Exception {
        doSlicingTest(
            "/slicing/methodContractAssignableRequestedLocation/MethodContractAssignableRequestedLocation.proof",
            new ReturnSelector(29), true, 23);
    }

    /**
     * Tests slicing on the example {@code methodContractAssignableEverything}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testMethodContractAssignableEverything() throws Exception {
        doSlicingTest(
            "/slicing/methodContractAssignableEverything/MethodContractAssignableExample.proof",
            new ReturnSelector(29), true, 23);
    }

    /**
     * Tests slicing on the example {@code equivalenceClassesTest} with equivalence classes at index
     * {@code 0}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testEquivalenceClasses_Index_1_no_OSS() throws Exception {
        doSlicingTest("/slicing/equivalenceClassesTest/Example_NoOSS.proof", new ReturnSelector(55),
            new EquivalenceClassByIndexSelector(1), // [Equivalence Class [a,b]]
            true, 38);
    }

    /**
     * Tests slicing on the example {@code equivalenceClassesTest} with equivalence classes at index
     * {@code 0}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testEquivalenceClasses_Index_0_no_OSS() throws Exception {
        doSlicingTest("/slicing/equivalenceClassesTest/Example_NoOSS.proof", new ReturnSelector(55),
            new EquivalenceClassByIndexSelector(0), // []
            true, 24);
    }

    /**
     * Tests slicing on the example {@code equivalenceClassesTest} with equivalence classes at index
     * {@code 0}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testEquivalenceClasses_Index_1() throws Exception {
        doSlicingTest("/slicing/equivalenceClassesTest/Example.proof", new ReturnSelector(27),
            new EquivalenceClassByIndexSelector(1), // [Equivalence Class [a,b]]
            true, 22);
    }

    /**
     * Tests slicing on the example {@code equivalenceClassesTest} with equivalence classes at index
     * {@code 0}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testEquivalenceClasses_Index_0() throws Exception {
        doSlicingTest("/slicing/equivalenceClassesTest/Example.proof", new ReturnSelector(27),
            new EquivalenceClassByIndexSelector(0), // []
            true, 17);
    }

    /**
     * Tests slicing on the example {@code aliasedByExecutionTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testAliasedByExecutionTest() throws Exception {
        doSlicingTest("/slicing/aliasedByExecutionTest/AliasedByExecution.proof",
            new ReturnSelector(41), true, 31);
    }

    /**
     * Tests slicing on the example {@code aliasedByExecutionTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testNotAliasedByExecutionTest() throws Exception {
        doSlicingTest("/slicing/aliasedByExecutionTest/AliasedByExecution.proof",
            new ReturnSelector(72), true, 17);
    }

    /**
     * Tests slicing on the example {@code loopInvariantNestedListFieldsTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testLoopInvariantNestedListFieldsTest() throws Exception {
        doSlicingTest(
            "/slicing/loopInvariantNestedListFieldsTest/LoopInvariantNestedListFieldsTest.proof",
            new ReturnSelector(424), true, 67);
    }

    /**
     * Tests slicing on the example {@code loopInvariantNotInListFieldsTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testLoopInvariantNotInListFieldsTest() throws Exception {
        doSlicingTest(
            "/slicing/loopInvariantNotInListFieldsTest/LoopInvariantNotInListFieldsTest.proof",
            new ReturnSelector(278), true, 13);
    }

    /**
     * Tests slicing on the example {@code loopInvariantInListFieldsTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testLoopInvariantInListFieldsTest() throws Exception {
        doSlicingTest("/slicing/loopInvariantInListFieldsTest/LoopInvariantInListFieldsTest.proof",
            new ReturnSelector(278), true, 15);
    }

    /**
     * Tests slicing on the example {@code loopInvariantStarFieldsTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testLoopInvariantStarFieldsTest() throws Exception {
        doSlicingTest("/slicing/loopInvariantStarFieldsTest/LoopInvariantStarFieldsTest.proof",
            new ReturnSelector(229), true, 13);
    }

    /**
     * Tests slicing on the example {@code simpleStaticLoopInvariantTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testSimpleStaticLoopInvariantTest() throws Exception {
        doSlicingTest("/slicing/simpleStaticLoopInvariantTest/SimpleStatiLoopInvariantTest.proof",
            new ReturnSelector(224), true, 12);
    }

    /**
     * Tests slicing on the example {@code simpleLoopInvariantTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testSimpleLoopInvariantTest() throws Exception {
        doSlicingTest("/slicing/simpleLoopInvariantTest/SimpleLoopInvariantTest.proof",
            new ReturnSelector(125), true, 9);
    }

    /**
     * Tests slicing on the example {@code arrayIndexAsVariableFieldTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testArrayIndexAsVariableFieldTest() throws Exception {
        doSlicingTest("/slicing/arrayIndexAsVariableFieldTest/ArrayIndexAsVariableFieldTest.proof",
            new ReturnSelector(412), true, 408, 397, 315, 256, 148);
    }

    /**
     * Tests slicing on the example {@code arrayIndexVariableTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testArrayIndexVariableTest() throws Exception {
        doSlicingTest("/slicing/arrayIndexVariableTest/ArrayIndexVariableTest.proof",
            new ReturnSelector(347), true, 343, 332, 258, 211, 118);
    }

    /**
     * Tests slicing on the example {@code arrayIndexSideeffectsBevore}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testArrayIndexSideeffectsBevore() throws Exception {
        doSlicingTest("/slicing/arrayIndexSideeffectsBevore/ArrayIndexSideeffectsBevore.proof",
            new ReturnSelector(211), true, 148, 55);
    }

    /**
     * Tests slicing on the example {@code arrayIndexSideeffectsAfter}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testArrayIndexSideeffectsAfter() throws Exception {
        doSlicingTest("/slicing/arrayIndexSideeffectsAfter/ArrayIndexSideeffectsAfter.proof",
            new ReturnSelector(216), true, 163, 59);
    }

    /**
     * Tests slicing on the example {@code simpleMultidimensionArrayTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testSimpleMultidimensionArrayTest() throws Exception {
        doSlicingTest("/slicing/simpleMultidimensionArrayTest/SimpleMultidimensionArrayTest.proof",
            new ReturnSelector(456), true, 440, 436, 411, 348, 172, 133);
    }

    /**
     * Tests slicing on the example {@code simpleArrayTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testSimpleArrayTest() throws Exception {
        doSlicingTest("/slicing/simpleArrayTest/SimpleArrayTest.proof", new ReturnSelector(163),
            false, 143, 36, 21);
    }

    /**
     * Tests slicing on the example {@code figure2Param}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testFigure2Param_right() throws Exception {
        doSlicingTest("/slicing/figure2Param/Figure2Param.proof", new RightAssignmentSelector(165),
            true, 151, 85);
    }

    /**
     * Tests slicing on the example {@code figure2Local}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testFigure2Local_right() throws Exception {
        doSlicingTest("/slicing/figure2Local/Figure2Local.proof",
            new RightVariableDeclarationSelector(168), true, 154, 86);
    }

    /**
     * Tests slicing on the example {@code figure2Instance}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testFigure2Instance_right() throws Exception {
        doSlicingTest("/slicing/figure2Instance/Figure2Instance.proof",
            new RightAssignmentSelector(267), true, 229, 182, 180, 165, 161, 144, 99);
    }

    /**
     * Tests slicing on the example {@code valueChange}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testValueChange() throws Exception {
        doSlicingTest("/slicing/valueChange/ValueChange.proof", new ReturnSelector(88), true, 84,
            72, 56, 52, 26);
    }

    /**
     * Tests slicing on the example {@code readWriteTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testReadWriteTest() throws Exception {
        doSlicingTest("/slicing/readWriteTest/ReadWriteTest.proof", new ReturnSelector(40), true,
            36, 29, 21, 11);
    }

    /**
     * Tests slicing on the example {@code aliasChanged}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testAliasChanged() throws Exception {
        doSlicingTest("/slicing/aliasChanged/AliasChanged.proof", new ReturnSelector(203), false,
            198, 194, 86, 57);
    }

    /**
     * Tests slicing on the example {@code aliasNotAvailable}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testAliasNotAvailable() throws Exception {
        doSlicingTest("/slicing/aliasNotAvailable/AliasNotAvailable.proof", new ReturnSelector(178),
            false, 173, 169, 98, 77);
    }

    /**
     * Tests slicing on the example {@code intEndTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testIntEndTest() throws Exception {
        doSlicingTest("/slicing/intEndTest/IntEndTest.proof", new ReturnSelector(17), false, 13,
            11);
    }

    /**
     * Tests slicing on the example {@code simpleAliasChanged}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testSimpleAliasChanged() throws Exception {
        doSlicingTest("/slicing/simpleAliasChanged/SimpleAliasChanged.proof",
            new ReturnSelector(36), false, 24);
    }

    /**
     * Tests slicing on the example {@code instanceFieldsAliased}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testInstanceFieldsAliased() throws Exception {
        doSlicingTest("/slicing/instanceFieldsAliased/InstanceFieldsAliased.proof",
            new ReturnSelector(185), false, 180, 176, 68);
    }

    /**
     * Tests slicing on the example {@code nestedInstanceFields}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testNestedInstanceFields() throws Exception {
        doSlicingTest("/slicing/nestedInstanceFields/NestedInstanceFields.proof",
            new ReturnSelector(142), false, 137, 133, 41, 27);
    }

    /**
     * Tests slicing on the example {@code methodCallTest}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testMethodCallTest() throws Exception {
        doSlicingTest("/slicing/methodCallTest/MethodCallTest.proof", new ReturnSelector(138),
            false, 98, 39, 15);
    }

    /**
     * Tests slicing on the example {@code aliasing}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testAliasing() throws Exception {
        doSlicingTest("/slicing/aliasing/Aliasing.proof", new ReturnSelector(62), false, 58, 20,
            15);
    }

    /**
     * Tests slicing on the example {@code nestedInstanceAccess}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testNestedInstanceAccess_subResult() throws Exception {
        doSlicingTest("/slicing/nestedInstanceAccess/NestedInstanceAccess.proof",
            new ReturnSelector(138), false, 136, 132, 127, 113, 86, 54, 39);
    }

    /**
     * Tests slicing on the example {@code figure2}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testFigure2_right() throws Exception {
        doSlicingTest("/slicing/figure2/Figure2.proof", new RightAssignmentSelector(269), false,
            229, 179);
    }

    /**
     * Tests slicing on the example {@code figure2}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testFigure2_left() throws Exception {
        doSlicingTest("/slicing/figure2/Figure2.proof", new LeftAssignmentSelector(269), false, 269,
            229, 179);
    }

    /**
     * Tests slicing on the example {@code simpleInstanceFields}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testSimpleInstanceFields() throws Exception {
        doSlicingTest("/slicing/simpleInstanceFields/SimpleInstanceFields.proof",
            new ReturnSelector(74), false, 69, 65, 18, 13);
    }

    /**
     * Tests slicing on the example {@code simpleThisInstanceFields}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testSimpleThisInstanceFields() throws Exception {
        doSlicingTest("/slicing/simpleThisInstanceFields/SimpleThisInstanceFields.proof",
            new ReturnSelector(48), false, 46, 42, 11, 9);
    }

    /**
     * Tests slicing on the example {@code simpleStaticFields}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testSimpleStaticFields() throws Exception {
        doSlicingTest("/slicing/simpleStaticFields/SimpleStaticFields.proof",
            new ReturnSelector(73), false, 59, 17, 10);
    }

    /**
     * Tests slicing on the example {@code simpleLocalVariables}.
     *
     * @throws Exception Occurred Exception.
     */
    @Test
    public void testSimpleLocalVariables() throws Exception {
        doSlicingTest("/slicing/simpleLocalVariables/SimpleLocalVariables.proof",
            new ReturnSelector(23), true, 19, 11, 7);
    }

    /**
     * Performs a slicing test.
     *
     * @param proofFileInRepository The path to the proof file.
     * @param selector The {@link ISeedLocationSelector} to use.
     * @param fullSlize {@code true} if the he full slice is given as expected slice and
     *        {@code false} if only a part of the slice is given as expected slice.
     * @param expectedSlice The serial IDs of the expected slices.
     * @throws Exception Occurred Exception
     */
    protected void doSlicingTest(String proofFileInRepository, ISeedLocationSelector selector,
            boolean fullSlize, int... expectedSlice) throws Exception {
        doSlicingTest(proofFileInRepository, selector, new NoEquivalenceClassSelector(), fullSlize,
            expectedSlice);
    }

    /**
     * Performs a slicing test.
     *
     * @param proofFileInRepository The path to the proof file.
     * @param selector The {@link ISeedLocationSelector} to use.
     * @param fullSlize {@code true} if the he full slice is given as expected slice and
     *        {@code false} if only a part of the slice is given as expected slice.
     * @param expectedSlice The serial IDs of the expected slices.
     * @throws Exception Occurred Exception
     */
    protected void doSlicingTest(String proofFileInRepository, ISeedLocationSelector selector,
            IEquivalenceClassSelector eqSelector, boolean fullSlize, int... expectedSlice)
            throws Exception {
        // Load proof
        File proofFile = new File(testCaseDirectory, proofFileInRepository);
        Assertions.assertTrue(proofFile.exists());
        KeYEnvironment<?> environment = KeYEnvironment.load(
            SymbolicExecutionJavaProfile.getDefaultInstance(), proofFile, null, null, null, true);
        try {
            // Get loaded proof
            Proof proof = environment.getLoadedProof();
            Assertions.assertNotNull(proof);
            // Find seed
            Pair<Node, ReferencePrefix> seed = selector.findSeed(proof);
            // Select equivalence class
            Assertions.assertNotNull(eqSelector);
            ImmutableList<ISymbolicEquivalenceClass> sec =
                eqSelector.selectEquivalenceClass(environment, proof, seed);
            if (PRINT_SLICE) {
                LOGGER.info("Equivalence Class: {}", sec);
            }
            // Perform slicing
            ThinBackwardSlicer slicer = new ThinBackwardSlicer();
            ImmutableArray<Node> slices = slicer.slice(seed.first, seed.second, sec);
            // Print slice if requested
            if (PRINT_SLICE) {
                LOGGER.info("Found Slices: {}", slices.size());
                for (Node slice : slices) {
                    LOGGER.info("SerialNr {}", slice.serialNr());
                }
            }
            if (fullSlize) {
                // Compare all Nodes in the slice
                Assertions.assertEquals(expectedSlice.length, slices.size());
                for (int i = 0; i < expectedSlice.length; i++) {
                    Node slice = slices.get(i);
                    Assertions.assertNotNull(slice);
                    Assertions.assertEquals(expectedSlice[i], slice.serialNr());
                }
            } else {
                // Ensure that only given Nodes exist in the slice maintaining the order
                int currentIndex = 0;
                for (int expected : expectedSlice) {
                    Node slice = null;
                    while (slice == null && currentIndex < slices.size()) {
                        Node toCheck = slices.get(currentIndex);
                        Assertions.assertNotNull(toCheck);
                        if (toCheck.serialNr() == expected) {
                            slice = toCheck;
                        }
                        currentIndex++;
                    }
                    Assertions.assertNotNull(slice);
                }
            }
        } finally {
            environment.dispose();
        }
    }

    /**
     * Implementations are used to select an {@link ISymbolicEquivalenceClass}.
     *
     * @author Martin Hentschel
     */
    protected interface IEquivalenceClassSelector {
        /**
         * Selects the {@link ISymbolicEquivalenceClass}.
         *
         * @param environment The current {@link KeYEnvironment}.
         * @param proof The current {@link Proof}.
         * @param seed The current seed.
         * @return The {@link ISymbolicEquivalenceClass}es or {@code null} to select.
         */
        ImmutableList<ISymbolicEquivalenceClass> selectEquivalenceClass(
                KeYEnvironment<?> environment, Proof proof, Pair<Node, ReferencePrefix> seed)
                throws Exception;
    }

    /**
     * An {@link IEquivalenceClassSelector} which selects no {@link ISymbolicEquivalenceClass}.
     *
     * @author Martin Hentschel
     */
    protected static class NoEquivalenceClassSelector implements IEquivalenceClassSelector {
        /**
         * {@inheritDoc}
         */
        @Override
        public ImmutableList<ISymbolicEquivalenceClass> selectEquivalenceClass(
                KeYEnvironment<?> environment, Proof proof, Pair<Node, ReferencePrefix> seed) {
            return null;
        }
    }

    /**
     * An {@link IEquivalenceClassSelector} which selects an {@link ISymbolicEquivalenceClass} by
     * index.
     *
     * @author Martin Hentschel
     */
    protected static class EquivalenceClassByIndexSelector implements IEquivalenceClassSelector {
        /**
         * The index of the {@link ISymbolicEquivalenceClass}es.
         */
        private final int index;

        /**
         * Constructor.
         *
         * @param index The index of the {@link ISymbolicEquivalenceClass}es.
         */
        public EquivalenceClassByIndexSelector(int index) {
            this.index = index;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public ImmutableList<ISymbolicEquivalenceClass> selectEquivalenceClass(
                KeYEnvironment<?> environment, Proof proof, Pair<Node, ReferencePrefix> seed)
                throws Exception {
            SymbolicExecutionTreeBuilder builder =
                new SymbolicExecutionTreeBuilder(proof, false, false, false, false, false);
            SymbolicExecutionUtil.initializeStrategy(builder);
            builder.analyse();
            IExecutionNode<?> node = builder.getExecutionNode(seed.first);
            assert node instanceof AbstractExecutionNode<?>;
            ExecutionNodeSymbolicLayoutExtractor extractor =
                ((AbstractExecutionNode<?>) node).getLayoutExtractor();
            return extractor.getEquivalenceClasses(index);
        }
    }

    /**
     * {@link ISeedLocationSelector} which searches the right side of a variable declaration.
     *
     * @author Martin Hentschel
     */
    protected static class RightVariableDeclarationSelector implements ISeedLocationSelector {
        /**
         * The serial ID of the seed node.
         */
        private final int seedNodeId;

        /**
         * Constructor.
         *
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
            Assertions.assertNotNull(seedNode);
            // Get seed location
            SourceElement activeStatemt = seedNode.getNodeInfo().getActiveStatement();
            Assertions.assertTrue(activeStatemt instanceof VariableDeclaration);
            VariableDeclaration variableDeclaration = (VariableDeclaration) activeStatemt;
            SourceElement seedLocation = variableDeclaration.getChildAt(1);
            Assertions.assertTrue(seedLocation instanceof VariableSpecification);
            return new Pair<>(seedNode,
                (ReferencePrefix) ((VariableSpecification) seedLocation).getInitializer());
        }
    }

    /**
     * {@link ISeedLocationSelector} which searches the right side of an assignment.
     *
     * @author Martin Hentschel
     */
    protected static class RightAssignmentSelector implements ISeedLocationSelector {
        /**
         * The serial ID of the seed node.
         */
        private final int seedNodeId;

        /**
         * Constructor.
         *
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
            Assertions.assertNotNull(seedNode);
            // Get seed location
            SourceElement activeStatemt = seedNode.getNodeInfo().getActiveStatement();
            Assertions.assertTrue(activeStatemt instanceof CopyAssignment);
            CopyAssignment assignment = (CopyAssignment) activeStatemt;
            SourceElement seedLocation = assignment.getChildAt(1);
            return new Pair<>(seedNode, (ReferencePrefix) seedLocation);
        }
    }

    /**
     * {@link ISeedLocationSelector} which searches the left side of an assignment.
     *
     * @author Martin Hentschel
     */
    protected static class LeftAssignmentSelector implements ISeedLocationSelector {
        /**
         * The serial ID of the seed node.
         */
        private final int seedNodeId;

        /**
         * Constructor.
         *
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
            Assertions.assertNotNull(seedNode);
            // Get seed location
            SourceElement activeStatemt = seedNode.getNodeInfo().getActiveStatement();
            Assertions.assertTrue(activeStatemt instanceof CopyAssignment);
            CopyAssignment assignment = (CopyAssignment) activeStatemt;
            SourceElement seedLocation = assignment.getChildAt(0);
            return new Pair<>(seedNode, (ReferencePrefix) seedLocation);
        }
    }

    /**
     * {@link ISeedLocationSelector} which searches a return expression as seed.
     *
     * @author Martin Hentschel
     */
    protected static class ReturnSelector implements ISeedLocationSelector {
        /**
         * The serial ID of the seed node.
         */
        private final int seedNodeId;

        /**
         * Constructor.
         *
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
            Assertions.assertNotNull(seedNode);
            // Get seed location
            SourceElement activeStatemt = seedNode.getNodeInfo().getActiveStatement();
            Assertions.assertTrue(activeStatemt instanceof Return);
            Return returnStatement = (Return) activeStatemt;
            SourceElement seedLocation = returnStatement.getExpression();
            return new Pair<>(seedNode, (ReferencePrefix) seedLocation);
        }
    }

    /**
     * Implementations of this interface are used to find the seed.
     *
     * @author Martin Hentschel
     */
    protected interface ISeedLocationSelector {
        Pair<Node, ReferencePrefix> findSeed(Proof proof);
    }

    /**
     * Searches a {@link Node} with the given serial ID.
     *
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
     *
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
         *
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
         *
         * @return The found {@link Node} or {@code null} if not available.
         */
        public Node getNode() {
            return node;
        }
    }
}
