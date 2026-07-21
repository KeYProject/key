/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * Regression test for bounded cross-multiplication of inequations in the DefOps arithmetic
 * treatment.
 *
 * <p>
 * The {@code multiply_2_inEq*} taclets used to be reachable only with the Model Search treatment.
 * They are now also enabled - restricted to products that are exactly bounded by an inequation
 * already present in the sequent, which keeps the strategy terminating - with DefOps. The pure
 * arithmetic problem in {@code crossMultDefOps.key} needs such a cross-multiplication, so it now
 * closes with DefOps as it does with Model Search, while Basic arithmetic still leaves it open.
 * </p>
 */
public class DefOpsCrossMultiplicationTest {

    private static final Path PROBLEM = FindResources.getTestResourcesDirectory()
            .resolve("de/uka/ilkd/key/strategy/crossMultDefOps.key");

    private boolean closesWith(String nonLinArithMode) throws Exception {
        KeYEnvironment<?> env = KeYEnvironment.load(PROBLEM);
        try {
            Proof proof = env.getLoadedProof();
            var settings = proof.getSettings().getStrategySettings();
            var sp = settings.getActiveStrategyProperties();
            sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, nonLinArithMode);
            settings.setActiveStrategyProperties(sp);
            settings.setMaxSteps(30000);
            proof.setActiveStrategy(
                proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));
            env.getProofControl().startAndWaitForAutoMode(proof);
            return proof.closed();
        } finally {
            env.dispose();
        }
    }

    @Test
    public void closesWithDefOps() throws Exception {
        Assertions.assertTrue(closesWith(StrategyProperties.NON_LIN_ARITH_DEF_OPS),
            "cross-multiplication should let DefOps close the index-in-bounds obligation");
    }

    @Test
    public void closesWithModelSearch() throws Exception {
        Assertions.assertTrue(closesWith(StrategyProperties.NON_LIN_ARITH_COMPLETION),
            "Model Search should still close the index-in-bounds obligation");
    }

    @Test
    public void staysOpenWithBasicArithmetic() throws Exception {
        Assertions.assertFalse(closesWith(StrategyProperties.NON_LIN_ARITH_NONE),
            "without non-linear arithmetic the obligation cannot be closed");
    }
}
