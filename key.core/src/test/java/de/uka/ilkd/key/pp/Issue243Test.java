/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import java.io.IOException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.prover.sequent.Sequent;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Regression test for issue #243: {@code LogicPrinter.printSemisequent} /
 * {@code quickPrintSemisequent} drops the last formula of the semisequent, while the same
 * formulas printed as part of a full sequent are rendered completely.
 */
class Issue243Test {

    @Test
    void quickPrintSemisequentDoesNotDropLastFormula() throws IOException {
        Services services = TacletForTests.services().copy(false);
        KeyIO io = new KeyIO(services, services.getNamespaces());

        Sequent seq = io.load("""
                \\problem { ==> true, false }
                """).loadCompleteProblem().getProblem();

        String semi = LogicPrinter.quickPrintSemisequent(seq.succedent(), services);
        String full = LogicPrinter.quickPrintSequent(seq, services);

        // The full sequent renders both formulas; the semisequent must render the same content.
        // Before the fix, the trailing formula is missing from the semisequent rendering.
        assertTrue(semi.contains("true") && semi.contains("false"),
            "quickPrintSemisequent dropped a formula. semisequent=<" + semi
                + ">, full sequent=<" + full + ">");
    }
}
