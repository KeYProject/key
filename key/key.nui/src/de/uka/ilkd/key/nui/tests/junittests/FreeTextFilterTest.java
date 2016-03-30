package de.uka.ilkd.key.nui.tests.junittests;

import static org.junit.Assert.assertEquals;

import java.io.File;

import org.antlr.runtime.tree.TreeFilter;
import org.junit.Test;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.DataModel;
import de.uka.ilkd.key.nui.TreeViewState;
import de.uka.ilkd.key.nui.controller.FilterViewController;
import de.uka.ilkd.key.nui.prooftree.FilteringHandler;
import de.uka.ilkd.key.nui.prooftree.ProofTreeConverter;
import de.uka.ilkd.key.nui.prooftree.ProofTreeItem;
import de.uka.ilkd.key.nui.prooftree.filter.ProofTreeFilter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * Test for User Story: Freitext-Filter im Beweisbaum.
 * 
 * @author Patrick Jattke
 *
 */
public class FreeTextFilterTest {

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
     * The proof file loaded in {@link #setUp(String)}.
     */
    private Proof proof;

    /**
     * The FilterViewController used to filter the tree.
     */
    private FilterViewController fvc;

    /**
     * Prepares the test environment and loads the proof tree.
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
        proof = environment.getLoadedProof();
        ptVisualizer = new ProofTreeConverter(proof);

        ProofTreeItem tree = ptVisualizer.createFXProofTree();
        DataModel dm = new DataModel(null, null);
        dm.setLoaddTriVwStat(new TreeViewState(proof, tree));

        fvc = new FilterViewController();
        fvc.setFilteringHandler(new FilteringHandler(dm));

        return tree;
    }

    /**
     * Test for the text filter applied to the {@link #TESTFILE_01}.
     */
    @Test
    public void testTextFilter_01_A() {
        ProofTreeItem tree = setUp(TESTFILE_01);
        filterTree(fvc, "and");
        int result = countFilteredItems(tree, fvc.getTextFilter(), 0);
        assertEquals(66, result);
    }

    /**
     * Test for the text filter applied to the {@link #TESTFILE_01}.
     */
    @Test
    public void testTextFilter_01_B() {
        ProofTreeItem tree = setUp(TESTFILE_01);
        filterTree(fvc, "alphaBetaGammDelta");
        int result = countFilteredItems(tree, fvc.getTextFilter(), 0);
        assertEquals(44, result);
    }

    /**
     * Test for the text filter applied to the {@link #TESTFILE_01}.
     */
    @Test
    public void testTextFilter_01_C() {
        ProofTreeItem tree = setUp(TESTFILE_01);
        filterTree(fvc, "add_lit");
        int result = countFilteredItems(tree, fvc.getTextFilter(), 0);
        assertEquals(84, result);
    }

    /**
     * Test for the text filter applied to the {@link #TESTFILE_02}.
     */
    @Test
    public void testTextFilter_02_A() {
        ProofTreeItem tree = setUp(TESTFILE_02);
        filterTree(fvc, " ");
        int result = countFilteredItems(tree, fvc.getTextFilter(), 0);
        assertEquals(7, result);
    }

    /**
     * Test for the text filter applied to the {@link #TESTFILE_02}.
     */
    @Test
    public void testTextFilter_02_B() {
        ProofTreeItem tree = setUp(TESTFILE_02);
        filterTree(fvc, "OPEN");
        int result = countFilteredItems(tree, fvc.getTextFilter(), 0);
        assertEquals(5, result);
    }

    /**
     * Test for the text filter applied to the {@link #TESTFILE_02}.
     */
    @Test
    public void testTextFilter_02_C() {
        ProofTreeItem tree = setUp(TESTFILE_02);
        filterTree(fvc, ":");
        int result = countFilteredItems(tree, fvc.getTextFilter(), 0);
        assertEquals(7, result);
    }

    /**
     * Test for the text filter applied to the {@link #TESTFILE_03}.
     */
    @Test
    public void testTextFilter_03_A() {
        ProofTreeItem tree = setUp(TESTFILE_03);
        filterTree(fvc, "concrete");
        int result = countFilteredItems(tree, fvc.getTextFilter(), 0);
        assertEquals(41, result);
    }

    /**
     * Test for the text filter applied to the {@link #TESTFILE_03}.
     */
    @Test
    public void testTextFilter_03_B() {
        ProofTreeItem tree = setUp(TESTFILE_03);
        filterTree(fvc, "goal");
        int result = countFilteredItems(tree, fvc.getTextFilter(), 0);
        assertEquals(21, result);
    }

    /**
     * Test for the text filter applied to the {@link #TESTFILE_03}.
     */
    @Test
    public void testTextFilter_03_C() {
        ProofTreeItem tree = setUp(TESTFILE_03);
        filterTree(fvc, "translate");
        int result = countFilteredItems(tree, fvc.getTextFilter(), 0);
        assertEquals(48, result);
    }

    /**
     * Filters the tree loaded in {@link #setUp(String)} by the given search
     * term.
     * 
     * @param fvc
     *            The FilterViewController associated with the tree to be
     *            filtered.
     * @param searchTerm
     *            The search term to be used as text filter for the inner nodes,
     *            see {@link FilteringHandler#filterBy(ProofTreeFilter).
     * 
     */
    private static void filterTree(FilterViewController fvc, String searchTerm) {
        fvc.setTerm(searchTerm);
        fvc.getFilteringHandler().filterBy(fvc.getTextFilter());
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
    private int countFilteredItems(final ProofTreeItem tree,
            final ProofTreeFilter filterType, final int accumulator) {
        int returnvalue = accumulator;
        if (tree.filter(filterType)) {
            returnvalue++;
            for (ProofTreeItem child : tree.getFilteredChildren()) {
                returnvalue += countFilteredItems(child, filterType, 0);
            }
        }
        return returnvalue;
    }

}
