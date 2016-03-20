package de.uka.ilkd.key.nui.tests.junittests;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Before;
import org.junit.Test;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.ProofTreeConverter;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * Test for User Story (005). Laden von Beweisen #14469
 * 
 * @author Patrick Jattke
 *
 */
public class SearchTest {

    /**
     * The proof file used for this test.
     */
    private static final String TESTFILE_01 = "resources//de/uka//ilkd//key//examples//example01.proof";

    /**
     * The ProofTreeVisualizer used to load the test file.
     */
    private static ProofTreeConverter ptVisualizer;

    /**
     * 
     */
    @Before
    public void setUp() {

        final File proofFile = new File(TESTFILE_01);
        KeYEnvironment<?> environment = null;
        try {
            environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null,
                    null, null, true);
        }
        catch (ProblemLoaderException e) {
            throw new RuntimeException("Could not set up testing environment.", e);
        }
        ptVisualizer = new ProofTreeConverter(environment.getLoadedProof());
    }

    /**
     * Checks whether {@link NUINode#asList()} works as expected.
     */
    @Test
    public void testAsList() {
        assertEquals(669 + 29, ptVisualizer.getRootNode().asList().stream().count());
    }

    /**
     * Test for standard search terms.
     */
    @Test
    public void testSearchNumberOfFindings() {
        // 01_CommonSearch
        final String searchTerm01 = "polySimp_pullOutFactor0b";
        assertTrue(searchAndCompareSize(searchTerm01, 6));

        // 02_CommonSearch
        final String searchTerm02 = "neg_literal";
        assertTrue(searchAndCompareSize(searchTerm02, 9));

        // 02_CommonSearch - test upper case
        assertTrue(searchAndCompareSize(searchTerm02.toUpperCase(), 9));

        // 03_CommonSearch
        final String searchTerm03 = "polySimp_";
        assertTrue(searchAndCompareSize(searchTerm03, 142));

        // 04_CommonSearch
        final String searchTerm04 = "inEqSimp_contradInEq0";
        assertTrue(searchAndCompareSize(searchTerm04, 4));

        // 04_CommonSearch - test upper case
        assertTrue(searchAndCompareSize(searchTerm04.toUpperCase(), 4));

        // 05_CommonSearch - test if beginning of term is found
        final String searchTerm05 = "qeq";
        assertTrue(searchAndCompareSize(searchTerm05, 49));

        // 05_CommonSearch - test upper case
        assertTrue(searchAndCompareSize(searchTerm05.toUpperCase(), 49));

        // 06_CommonSearch
        final String searchTerm06 = "CUT: a <= -1 | a >= 1 FALSE";
        assertTrue(searchAndCompareSize(searchTerm06, 2));

    }

    /**
     * Tests for search terms which return no matches.
     */
    @Test
    public void testSearchNoMatches() {
        // 01_NoMatchSearch
        final String searchTerm01 = "NO_SUCH";
        assertTrue(searchAndCompareSize(searchTerm01, 0));

        // 02_NoMatchSearch
        final String searchTerm02 = "polySimp_addAssoc2";
        assertTrue(searchAndCompareSize(searchTerm02, 0));

        // 03_NoMatchSearch
        final String searchTerm03 = "concrete_impl_2";
        assertTrue(searchAndCompareSize(searchTerm03, 0));

        // 04_NoMatchSearch
        final String searchTerm04 = "EQU$Simp";
        assertTrue(searchAndCompareSize(searchTerm04, 0));

        // 05_NoMatchSearch
        final String searchTerm05 = "polyS%imp-";
        assertTrue(searchAndCompareSize(searchTerm05, 0));

        // 06_NoMatchSearch
        final String searchTerm06 = "";
        assertTrue(searchAndCompareSize(searchTerm06, 0));

    }

    /**
     * Tests for search terms containing special characters, like spaces, |, _,
     * etc.
     */
    @Test
    public void testSearchSpecialTerms() {
        // 01_NoMatchSearch
        final String searchTerm01 = "CUT: a >= 1 TRUE";
        assertTrue(searchAndCompareSize(searchTerm01, 1));

        // 02_NoMatchSearch
        final String searchTerm02 = "CUT: a <= -2 | a >= 2 FALSE";
        assertTrue(searchAndCompareSize(searchTerm02, 1));

        // 03_NoMatchSearch
        final String searchTerm03 = "$leq";
        assertTrue(searchAndCompareSize(searchTerm03, 0));

    }

    /**
     * Searches for the given searchTerm and compares the size of the results
     * with the given expectedSize.
     * 
     * @param searchTerm
     *            The term which should be used to search for.
     * @param expectedSize
     *            The expected size of the list of results.
     * @return True iff the size of the result list equals the expectedSize.
     */

    private static boolean searchAndCompareSize(final String searchTerm, final int expectedSize) {
        ptVisualizer.getRootNode().search(searchTerm);
        return expectedSize == ptVisualizer.getRootNode().asList().stream()
                .filter((node) -> node.isSearchResult()).count();
    }

}
