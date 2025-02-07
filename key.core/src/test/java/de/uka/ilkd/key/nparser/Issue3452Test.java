/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.io.File;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * @author Alexander Weigl
 * @version 1 (31.01.25)
 */
public class Issue3452Test {


    @Test
    void testNoStateParsedCorrectly() throws ProblemLoaderException, ProofInputException {
        final var input =
            new File(
                "src/test/resources/de/uka/ilkd/key/nparser/fix3452/fix/Issue3452Fixture.java");
        var env = KeYEnvironment.load(input, null, null, null);
        final var contract = env.getProofContracts().getFirst();
        var po = contract.createProofObl(env.getInitConfig(), contract);
        var proof = env.createProof(po); // just to ensure there is exception
        Services services = proof.getInitConfig().getServices();
        Namespace<JFunction> functions = services.getNamespaces().functions();
        assertEquals("[int]", functions.lookup("A::b").argSorts().toString());
        assertEquals("[Heap,int]", functions.lookup("A::c").argSorts().toString());
    }

    @Test
    void testIllegalNoState() throws ProblemLoaderException, ProofInputException {
        final var input =
            new File(
                "src/test/resources/de/uka/ilkd/key/nparser/fix3452/problem/Issue3452IllegalNoState.java");

        ProblemLoaderException exception = assertThrows(ProblemLoaderException.class, () -> {
            var env = KeYEnvironment.load(input, null, null, null);
            System.err.println(env);
            System.err.println("Unexpected load success");
        });

        if (!exception.getMessage().startsWith("Heap used in a `no_state` method.")) {
            fail("Unexpected exception message: " + exception.getMessage());
        }
    }
}
