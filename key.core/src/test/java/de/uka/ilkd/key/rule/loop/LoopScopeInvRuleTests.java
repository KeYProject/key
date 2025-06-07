/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.loop;

import java.nio.file.Path;
import java.util.Objects;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.rule.merge.MergeRuleTests;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * Test cases for the {@link LoopScopeInvariantRule}. Should shine a light on more subtle and exotic
 * cases, like nested loops with multiple labeled breaks and continues, combination with exceptional
 * behavior / try-catch, etc.
 * <p>
 * TODO: Add more test cases for the scenarios sketched above.
 *
 * @author Dominic Scheurer
 */
public class LoopScopeInvRuleTests {
    private static final Path TEST_RESOURCES_DIR_PREFIX =
        HelperClassForTests.TESTCASE_DIRECTORY.resolve("loopScopeInvRule/");

    /**
     * Automatic proof of a benchmark with labeled breaks and continues.
     */
    @Test
    public void testDoAutomaticProofOfBenchmarkWithLabeledBreaksAndContinues() {
        final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX, "Test.key");
        MergeRuleTests.startAutomaticStrategy(proof);

        Assertions.assertTrue(Objects.requireNonNull(proof).closed());
    }

}
