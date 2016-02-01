package de.uka.ilkd.key.nui.tests.junittests;

import static org.junit.Assert.*;

import java.io.File;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.controller.TreeViewController;
import de.uka.ilkd.key.nui.prooftree.ProofTreeVisualizer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

public class NUIBranchNodeTests {

    private static String TESTFILE_01 = "resources//de/uka//ilkd//key//examples//example01.proof";
    private static ProofTreeVisualizer ptVisualizer;
    
    @BeforeClass
    public static void setUpBeforeClass() {        
        ptVisualizer = new ProofTreeVisualizer(null);
        File proofFile = new File(TESTFILE_01);
        KeYEnvironment<?> environment = null;
        try {
            environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
                    proofFile, null, null, null, true);
        }
        catch (ProblemLoaderException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        Proof proof = environment.getLoadedProof();
        ptVisualizer.loadProofTree(proof);
    }
    
    /**
     * Test for standard search terms.
     */
    @Test
    public void testSearchNumberOfFindings() {
        String SEARCH_TERM_01 = "polySimp_pullOutFactor0b";
        String SEARCH_TERM_02 = "neg_literal";
        String SEARCH_TERM_03 = "polySimp_rightDist";
        String SEARCH_TERM_04 = "inEqSimp_contradInEq0";
        String SEARCH_TERM_05 = "qeq_literals";
        String SEARCH_TERM_06 = "CUT: a <= -1 | a >= 1 FALSE";
        
        // Search01
        assertTrue(searchAndCompareSize(SEARCH_TERM_01, 6));
        
        // Search02
        assertTrue(searchAndCompareSize(SEARCH_TERM_02, 9));
        
        // Search03
        assertTrue(searchAndCompareSize(SEARCH_TERM_03, 25));
        
        // Search04
        assertTrue(searchAndCompareSize(SEARCH_TERM_04, 4));
        
        // Search05
        assertTrue(searchAndCompareSize(SEARCH_TERM_05, 49));
        
        // Search06
        assertTrue(searchAndCompareSize(SEARCH_TERM_06, 2));
    }  
    
    
    /**
     * Tests for search terms which return no matches.
     */
    @Test
    public void testSearchNoMatches() {
        
    }
    
    /**
     * Tests for search terms containing special characters,
     * like spaces, &, $, etc.
     */
    @Test
    public void testSearchSpecialTerms() {
        
    }
    
    private boolean searchAndCompareSize(String searchTerm, int expectedSize) {
        /*
         * int NoOfFindings = ptVisualizer.getRootNode().search(searchTerm).size();
         * return (NoOfFindings == expectedSize);         
         */
        return false;
    }

}
