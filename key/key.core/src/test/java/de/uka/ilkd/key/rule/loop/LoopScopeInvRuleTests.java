// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.loop;

import org.junit.Test;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.rule.merge.MergeRuleTests;
import junit.framework.TestCase;

/**
 * Test cases for the {@link LoopScopeInvariantRule}. Should shine a light on
 * more subtle and exotic cases, like nested loops with multiple labeled breaks
 * and continues, combination with exceptional behavior / try-catch, etc.
 * 
 * TODO: Add more test cases for the scenarios sketched above.
 *
 * @author Dominic Scheurer
 */
public class LoopScopeInvRuleTests extends TestCase {

    private static final String TEST_RESOURCES_DIR_PREFIX = "resources/testcase/loopScopeInvRule/";

    /**
     * Automatic proof of a benchmark with labeled breaks and continues.
     */
    @Test
    public void testDoAutomaticProofOfBenchmarkWithLabeledBreaksAndContinues() {
        final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX,
                "Test.key");
        MergeRuleTests.startAutomaticStrategy(proof);

        assertTrue(proof.closed());
    }

}
