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
 * Test for User Story.
 * - #14469 Suchen im Beweisbaum
 * 
 * @author Patrick Jattke
 *
 */
@SuppressWarnings({"PMD.BeanMembersShouldSerialize", "PMD.AtLeastOneConstructor"})
// Why would anyone ever serialize a JUnit Test?
//PMD will also complain after adding a constructor, then saying "avoid useless constructors"
public class SearchTest {
    /**
     * A few pairs of a search term and the expected number of results.
     */
    private static final String SEARCH_TERM_01 = "polySimp_pullOutFactor0b";
    private static final int NUM_RESULTS_01 = 6;
    private static final String SEARCH_TERM_02 = "neg_literal";
    private static final int NUM_RESULTS_02 = 9;
    private static final String SEARCH_TERM_03 = "polySimp_";
    private static final int NUM_RESULTS_03 = 142;
    private static final String SEARCH_TERM_04 = "inEqSimp_contradInEq0";
    private static final int NUM_RESULTS_04 = 4;
    private static final String SEARCH_TERM_05 = "qeq";
    private static final int NUM_RESULTS_05 = 49;
    private static final String SEARCH_TERM_06 = "CUT: a <= -1 | a >= 1 FALSE";
    private static final int NUM_RESULTS_06 = 2;
    private static final String SEARCH_TERM_11 = "CUT: a >= 1 TRUE";
    private static final int NUM_RESULTS_11 = 1;
    private static final String SEARCH_TERM_12 = "CUT: a <= -2 | a >= 2 FALSE";
    private static final int NUM_RESULTS_12 = 1;
    private static final String SEARCH_TERM_13 = "$leq";
    private static final int NUM_RESULTS_13 = 0;
    private static final String SEARCH_TERM_21 = "NO_SUCH";
    private static final int NUM_RESULTS_21 = 0;
    private static final String SEARCH_TERM_22 = "polySimp_addAssoc2";
    private static final int NUM_RESULTS_22 = 0;
    private static final String SEARCH_TERM_23 = "concrete_impl_2";
    private static final int NUM_RESULTS_23 = 0;
    private static final String SEARCH_TERM_24 = "EQU$Simp";
    private static final int NUM_RESULTS_24 = 0;
    private static final String SEARCH_TERM_25 = "polyS%imp-";
    private static final int NUM_RESULTS_25 = 0;
    private static final String SEARCH_TERM_26 = "";
    private static final int NUM_RESULTS_26 = 0;

    /**
     * The proof file used for this test.
     */
    private static final String TESTFILE_01
        = "resources//de/uka//ilkd//key//examples//example01.proof";

    /**
     * The ProofTreeVisualizer used to load the test file.
     */
    private ProofTreeConverter ptVisualizer;

    /**
     * 
     */
    @Before
    public void setUp() {
        KeYEnvironment<?> environment = null;
        try {
            final File proofFile = new File(TESTFILE_01);
            environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null,
                    null, null, true);
        }
        catch (ProblemLoaderException e) {
            throw new IllegalStateException("Could not set up testing environment.", e);
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
        assertTrue(searchAndCompareSize(SEARCH_TERM_01, NUM_RESULTS_01));

        // 02_CommonSearch
        assertTrue(searchAndCompareSize(SEARCH_TERM_02, NUM_RESULTS_02));
        // 02_CommonSearch - test upper case
        assertTrue(searchAndCompareSize(SEARCH_TERM_02.toUpperCase(), NUM_RESULTS_02));

        // 03_CommonSearch
        assertTrue(searchAndCompareSize(SEARCH_TERM_03, NUM_RESULTS_03));

        // 04_CommonSearch
        assertTrue(searchAndCompareSize(SEARCH_TERM_04, NUM_RESULTS_04));
        // 04_CommonSearch - test upper case
        assertTrue(searchAndCompareSize(SEARCH_TERM_04.toUpperCase(), NUM_RESULTS_04));

        // 05_CommonSearch - test if beginning of term is found
        assertTrue(searchAndCompareSize(SEARCH_TERM_05, NUM_RESULTS_05));
        // 05_CommonSearch - test upper case
        assertTrue(searchAndCompareSize(SEARCH_TERM_05.toUpperCase(), NUM_RESULTS_05));

        // 06_CommonSearch
       assertTrue(searchAndCompareSize(SEARCH_TERM_06, NUM_RESULTS_06));

    }

    /**
     * Tests for search terms which return no matches.
     */
    @Test
    public void testSearchNoMatches() {
        // 01_NoMatchSearch
       assertTrue(searchAndCompareSize(SEARCH_TERM_21, NUM_RESULTS_21));

        // 02_NoMatchSearch
        assertTrue(searchAndCompareSize(SEARCH_TERM_22, NUM_RESULTS_22));

        // 03_NoMatchSearch
        assertTrue(searchAndCompareSize(SEARCH_TERM_23, NUM_RESULTS_23));

        // 04_NoMatchSearch
        assertTrue(searchAndCompareSize(SEARCH_TERM_24, NUM_RESULTS_24));

        // 05_NoMatchSearch
        assertTrue(searchAndCompareSize(SEARCH_TERM_25, NUM_RESULTS_25));

        // 06_NoMatchSearch
        assertTrue(searchAndCompareSize(SEARCH_TERM_26, NUM_RESULTS_26));

    }

    /**
     * Tests for search terms containing special characters, like spaces, |, _,
     * etc.
     */
    @Test
    public void testSearchSpecialTerms() {
        // 01_NoMatchSearch
        assertTrue(searchAndCompareSize(SEARCH_TERM_11, NUM_RESULTS_11));

        // 02_NoMatchSearch
        assertTrue(searchAndCompareSize(SEARCH_TERM_12, NUM_RESULTS_12));

        // 03_NoMatchSearch
        assertTrue(searchAndCompareSize(SEARCH_TERM_13, NUM_RESULTS_13));

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
