package de.uka.ilkd.key.nui.tests.junittests;

import static org.junit.Assert.*;
import java.io.File;
import org.junit.BeforeClass;
import org.junit.Test;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.prooftree.ProofTreeVisualizer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * Test for User Story (005) Laden von Beweisen #14469
 * 
 * @author Patrick Jattke
 *
 */
public class SearchTest {

    /**
     * The proof file used for this test.
     */
    private final static String TESTFILE_01 = "resources//de/uka//ilkd//key//examples//example01.proof";

    /**
     * The ProofTreeVisualizer used to load the test file.
     */
    private static ProofTreeVisualizer ptVisualizer;

    @BeforeClass
    public static void setUpBeforeClass() {
        ptVisualizer = new ProofTreeVisualizer(null);
        final File proofFile = new File(TESTFILE_01);
        KeYEnvironment<?> environment = null;
        try {
            environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
                    proofFile, null, null, null, true);
            final Proof proof = environment.getLoadedProof();
            ptVisualizer.loadProofTree(proof);
        }
        catch (ProblemLoaderException e) {
            fail("Could not set up testing environment.");
        }
    }

    @Test
    public void testAsList() {
        assertEquals(669 + 29,
                ptVisualizer.getRootNode().asList().stream().count());
    }

    /**
     * Test for standard search terms.
     */
    @Test
    public void testSearchNumberOfFindings() {
        // 01_CommonSearch
        final String SEARCH_TERM_01 = "polySimp_pullOutFactor0b";
        assertTrue(searchAndCompareSize(SEARCH_TERM_01, 6));

        // 02_CommonSearch
        final String SEARCH_TERM_02 = "neg_literal";
        assertTrue(searchAndCompareSize(SEARCH_TERM_02, 9));
        // 02_CommonSearch - test upper case
        assertTrue(searchAndCompareSize(SEARCH_TERM_02.toUpperCase(), 9));

        // 03_CommonSearch
        final String SEARCH_TERM_03 = "polySimp_";
        assertTrue(searchAndCompareSize(SEARCH_TERM_03, 142));

        // 04_CommonSearch
        final String SEARCH_TERM_04 = "inEqSimp_contradInEq0";
        assertTrue(searchAndCompareSize(SEARCH_TERM_04, 4));
        // 04_CommonSearch - test upper case
        assertTrue(searchAndCompareSize(SEARCH_TERM_04.toUpperCase(), 4));

        // 05_CommonSearch - test if beginning of term is found
        final String SEARCH_TERM_05 = "qeq";
        assertTrue(searchAndCompareSize(SEARCH_TERM_05, 49));
        // 05_CommonSearch - test upper case
        assertTrue(searchAndCompareSize(SEARCH_TERM_05.toUpperCase(), 49));

        // 06_CommonSearch
        final String SEARCH_TERM_06 = "CUT: a <= -1 | a >= 1 FALSE";
        assertTrue(searchAndCompareSize(SEARCH_TERM_06, 2));
    }

    /**
     * Tests for search terms which return no matches.
     */
    @Test
    public void testSearchNoMatches() {
        // 01_NoMatchSearch
        final String SEARCH_TERM_01 = "NO_SUCH";
        assertTrue(searchAndCompareSize(SEARCH_TERM_01, 0));

        // 02_NoMatchSearch
        final String SEARCH_TERM_02 = "polySimp_addAssoc2";
        assertTrue(searchAndCompareSize(SEARCH_TERM_02, 0));

        // 03_NoMatchSearch
        final String SEARCH_TERM_03 = "concrete_impl_2";
        assertTrue(searchAndCompareSize(SEARCH_TERM_03, 0));

        // 04_NoMatchSearch
        final String SEARCH_TERM_04 = "EQU$Simp";
        assertTrue(searchAndCompareSize(SEARCH_TERM_04, 0));

        // 05_NoMatchSearch
        final String SEARCH_TERM_05 = "polyS%imp-";
        assertTrue(searchAndCompareSize(SEARCH_TERM_05, 0));

        // 06_NoMatchSearch
        final String SEARCH_TERM_06 = "";
        assertTrue(searchAndCompareSize(SEARCH_TERM_06, 0));
    }

    /**
     * Tests for search terms containing special characters, like spaces, |, _,
     * etc.
     */
    @Test
    public void testSearchSpecialTerms() {
        // 01_NoMatchSearch
        final String SEARCH_TERM_01 = "CUT: a >= 1 TRUE";
        assertTrue(searchAndCompareSize(SEARCH_TERM_01, 1));

        // 02_NoMatchSearch
        final String SEARCH_TERM_02 = "CUT: a <= -2 | a >= 2 FALSE";
        assertTrue(searchAndCompareSize(SEARCH_TERM_02, 1));

        // 03_NoMatchSearch
        final String SEARCH_TERM_03 = "$leq";
        assertTrue(searchAndCompareSize(SEARCH_TERM_03, 0));
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
    private boolean searchAndCompareSize(final String searchTerm, final int expectedSize) {
        ptVisualizer.getRootNode().search(searchTerm);
        return expectedSize == ptVisualizer.getRootNode().asList().stream()
                .filter((node) -> node.isSearchResult()).count();
    }

}
