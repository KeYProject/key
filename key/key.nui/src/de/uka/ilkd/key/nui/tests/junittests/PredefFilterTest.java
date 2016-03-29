package de.uka.ilkd.key.nui.tests.junittests;

import static org.junit.Assert.assertEquals;

import java.io.File;

import org.antlr.runtime.tree.TreeFilter;
import org.junit.Test;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.prooftree.ProofTreeConverter;
import de.uka.ilkd.key.nui.prooftree.ProofTreeItem;
import de.uka.ilkd.key.nui.prooftree.filter.FilterCombineAND;
import de.uka.ilkd.key.nui.prooftree.filter.FilterHideClosed;
import de.uka.ilkd.key.nui.prooftree.filter.FilterHideIntermediate;
import de.uka.ilkd.key.nui.prooftree.filter.FilterHideNonInteractive;
import de.uka.ilkd.key.nui.prooftree.filter.FilterHideNonSymbolicExecution;
import de.uka.ilkd.key.nui.prooftree.filter.FilterShowAll;
import de.uka.ilkd.key.nui.prooftree.filter.ProofTreeFilter;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * Test for User Story: Vordefinierte Filter im Beweisbaum.
 * 
 * @author Patrick Jattke
 *
 */
public class PredefFilterTest {

    /**
     * The proof file 1 used for this test.
     */
    private static final String TESTFILE_01 = "resources//de/uka//ilkd//key//examples//example01.proof";

    /**
     * The proof file 2 used for this test.
     */
    private static final String TESTFILE_02 = "resources//de/uka//ilkd//key//examples//example02.proof";

    /**
     * The proof file 3 used for this test.
     */
    private static final String TESTFILE_03 = "resources//de/uka//ilkd//key//examples//gcd.twoJoins.proof";

    /**
     * The ProofTreeVisualizer used to load the test file.
     */
    private ProofTreeConverter ptVisualizer;

    /**
     * 
     */
    public ProofTreeItem setUp(String proofFileName) {
        final File proofFile = new File(proofFileName);
        KeYEnvironment<?> environment;
        try {
            environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
                    proofFile, null, null, null, true);
        }
        catch (ProblemLoaderException e) {
            throw new IllegalStateException(
                    "Could not set up testing environment.", e);
        }
        ptVisualizer = new ProofTreeConverter(environment.getLoadedProof());
        return ptVisualizer.createFXProofTree();
    }

    /**
     * Test for the filter {@link FilterShowAll}.
     */
    @Test
    public void testFilterShowAll_01() {
        ProofTreeItem tree = setUp(TESTFILE_01);
        int result = countFilteredItems(tree, new FilterShowAll(), 0);
        assertEquals(tree.getValue().asList().stream().count(), result);
    }

    /**
     * Test for the filter {@link FilterShowAll}.
     */
    @Test
    public void testFilterShowAll_02() {
        ProofTreeItem tree = setUp(TESTFILE_02);
        int result = countFilteredItems(tree, new FilterShowAll(), 0);
        assertEquals(tree.getValue().asList().stream().count(), result);
    }

    /**
     * Test for the filter {@link FilterShowAll}.
     */
    @Test
    public void testFilterShowAll_03() {
        ProofTreeItem tree = setUp(TESTFILE_03);
        int result = countFilteredItems(tree, new FilterShowAll(), 0);
        assertEquals(tree.getValue().asList().stream().count(), result);
    }

    /**
     * Test for the filter {@link FilterHideNonSymbolicExecution}.
     */
    @Test
    public void testFilterHideNonSymbolicExecution_01() {
        ProofTreeItem tree = setUp(TESTFILE_01);
        int result = countFilteredItems(tree,
                new FilterHideNonSymbolicExecution(), 0);
        assertEquals(44, result);
    }

    /**
     * Test for the filter {@link FilterHideNonSymbolicExecution}.
     */
    @Test
    public void testFilterHideNonSymbolicExecution_02() {
        ProofTreeItem tree = setUp(TESTFILE_02);
        int result = countFilteredItems(tree,
                new FilterHideNonSymbolicExecution(), 0);
        assertEquals(6, result);
    }

    /**
     * Test for the filter {@link FilterHideNonSymbolicExecution}.
     */
    @Test
    public void testFilterHideNonSymbolicExecution_03() {
        ProofTreeItem tree = setUp(TESTFILE_03);
        int result = countFilteredItems(tree,
                new FilterHideNonSymbolicExecution(), 0);
        assertEquals(75, result);
    }

    /**
     * Test for the filter {@link FilterHideNonInteractive}.
     */
    @Test
    public void testFilterHideNonInteractive_01() {
        ProofTreeItem tree = setUp(TESTFILE_01);
        int result = countFilteredItems(tree, new FilterHideNonInteractive(),
                0);
        assertEquals(44, result);
    }

    /**
     * Test for the filter {@link FilterHideNonInteractive}.
     */
    @Test
    public void testFilterHideNonInteractive_02() {
        ProofTreeItem tree = setUp(TESTFILE_02);
        int result = countFilteredItems(tree, new FilterHideNonInteractive(),
                0);
        assertEquals(5, result);
    }

    /**
     * Test for the filter {@link FilterHideNonInteractive}.
     */
    @Test
    public void testFilterHideNonInteractive_03() {
        ProofTreeItem tree = setUp(TESTFILE_03);
        int result = countFilteredItems(tree, new FilterHideNonInteractive(),
                0);
        assertEquals(23, result);
    }

    /**
     * Test for the filter {@link FilterHideIntermediate}.
     */
    @Test
    public void testFilterHideIntermediate_01() {
        ProofTreeItem tree = setUp(TESTFILE_01);
        int result = countFilteredItems(tree, new FilterHideIntermediate(), 0);
        assertEquals(44, result);
    }

    /**
     * Test for the filter {@link FilterHideIntermediate}.
     */
    @Test
    public void testFilterHideIntermediate_02() {
        ProofTreeItem tree = setUp(TESTFILE_02);
        int result = countFilteredItems(tree, new FilterHideIntermediate(), 0);
        assertEquals(5, result);
    }

    /**
     * Test for the filter {@link FilterHideIntermediate}.
     */
    @Test
    public void testFilterHideIntermediate_03() {
        ProofTreeItem tree = setUp(TESTFILE_03);
        int result = countFilteredItems(tree, new FilterHideIntermediate(), 0);
        assertEquals(21, result);
    }

    /**
     * Test for the filter {@link FilterHideClosed}.
     */
    @Test
    public void testFilterHideClosed_01() {
        ProofTreeItem tree = setUp(TESTFILE_01);
        int result = countFilteredItems(tree, new FilterHideClosed(), 0);
        assertEquals(0, result);
    }

    /**
     * Test for the filter {@link FilterHideClosed}.
     */
    @Test
    public void testFilterHideClosed_02() {
        ProofTreeItem tree = setUp(TESTFILE_02);
        int result = countFilteredItems(tree, new FilterHideClosed(), 0);
        assertEquals(7, result);
    }

    /**
     * Test for the filter {@link FilterHideClosed}.
     */
    @Test
    public void testFilterHideClosed_03() {
        ProofTreeItem tree = setUp(TESTFILE_03);
        int result = countFilteredItems(tree, new FilterHideClosed(), 0);
        assertEquals(550, result);
    }

    /**
     * Test for the filter {@link FilterCombineAND}.
     */
    @Test
    public void testFilterCombineAND1_01() {
        ProofTreeItem tree = setUp(TESTFILE_01);
        FilterCombineAND filterAND = new FilterCombineAND(
                new FilterHideIntermediate(), new FilterHideClosed());
        int result = countFilteredItems(tree, filterAND, 0);
        assertEquals(0, result);
    }

    /**
     * Test for the filter {@link FilterCombineAND}.
     */
    @Test
    public void testFilterCombineAND1_02() {
        ProofTreeItem tree = setUp(TESTFILE_02);
        FilterCombineAND filterAND = new FilterCombineAND(
                new FilterHideIntermediate(), new FilterHideClosed());
        int result = countFilteredItems(tree, filterAND, 0);
        assertEquals(5, result);
    }

    /**
     * Test for the filter {@link FilterCombineAND}.
     */
    @Test
    public void testFilterCombineAND1_03() {
        ProofTreeItem tree = setUp(TESTFILE_03);
        FilterCombineAND filterAND = new FilterCombineAND(
                new FilterHideIntermediate(), new FilterHideClosed());
        int result = countFilteredItems(tree, filterAND, 0);
        assertEquals(17, result);
    }

    /**
     * Test for the filter {@link FilterCombineAND}.
     */
    @Test
    public void testFilterCombineAND2_03() {
        ProofTreeItem tree = setUp(TESTFILE_03);
        FilterCombineAND filterAND1 = new FilterCombineAND(
                new FilterHideNonInteractive(), new FilterHideClosed());
        FilterCombineAND filterAND2 = new FilterCombineAND(filterAND1,
                new FilterHideNonSymbolicExecution());
        int result = countFilteredItems(tree, filterAND2, 0);
        assertEquals(19, result);
    }

    /**
     * Counts the {@link ProofTreeItem ProofTreeItems} in the given tree after
     * applying the {@link ProofTreeFilter} filterType by traversing the tree
     * and accumulating the number of nodes in the accumulator.
     * 
     * @param tree
     *            the {@link ProofTreeItem} tree which should be filtered.
     * @param filterType
     *            the {@link TreeFilter} to be used as filter.
     * @param accumulator
     *            should be 0 by the initial call, is used to accumulate the
     *            filtered nodes.
     * @return the number of nodes after applying the filter.
     */
    private int countFilteredItems(ProofTreeItem tree,
            ProofTreeFilter filterType, int accumulator) {
        if (tree.filter(filterType)) {
            accumulator++;
            for (ProofTreeItem child : tree.getFilteredChildren()) {
                accumulator += countFilteredItems(child, filterType, 0);
            }
        }
        return accumulator;
    }

}
