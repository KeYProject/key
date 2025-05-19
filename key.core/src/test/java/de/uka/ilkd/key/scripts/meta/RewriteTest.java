/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptException;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

public class RewriteTest {

    /**
     * Test for finding `f=x` and replacing it with `x=f` Taclet to be found and applied: eqSymm on
     * `f=x`
     */
    @Test
    public void testTransitive()
            throws IOException, ScriptException, InterruptedException, ProblemLoaderException {
        Path script = HelperClassForTests.TESTCASE_DIRECTORY.toPath()
                .resolve("scriptCommands/rewrite.script");
        File keyFile =
            new File(HelperClassForTests.TESTCASE_DIRECTORY, "scriptCommands/transitive.key");

        assumeTrue(Files.exists(script), "Required script file not found: " + script);
        assumeTrue(keyFile.exists(), "Required KeY file not found: " + keyFile);

        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        assertNotNull(env);

        Proof p = env.getLoadedProof();
        ProofScriptEngine engine = new ProofScriptEngine(script);
        engine.execute(env.getUi(), p);

        String firstOpenGoal = p.openGoals().head().sequent().toString();
        String expectedSequent = "[equals(x,f),equals(x,z)]==>[equals(z,f)]";

        System.out.println(p);
        assertEquals(expectedSequent, firstOpenGoal);
    }

    /**
     * Test for finding `f<x` and replacing it with `x>f` Taclet to be found and applied: lt_to_gt
     * on `f>x`
     */
    @Test
    public void testLessTransitive()
            throws IOException, ScriptException, InterruptedException, ProblemLoaderException {
        Path script = HelperClassForTests.TESTCASE_DIRECTORY.toPath()
                .resolve("scriptCommands/lesstrans.script");
        File keyFile =
            new File(HelperClassForTests.TESTCASE_DIRECTORY, "scriptCommands/less_trans.key");

        assumeTrue(Files.exists(script), "Required script file not found: " + script);
        assumeTrue(keyFile.exists(), "Required KeY file not found: " + keyFile);

        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        Proof proof = env.getLoadedProof();
        ProofScriptEngine engine = new ProofScriptEngine(script);
        engine.execute(env.getUi(), proof);

        String firstOpenGoal = proof.openGoals().head().sequent().toString();
        String expectedSequent = "[]==>[imp(and(gt(x,f),lt(x,z)),lt(f,z))]";

        assertEquals(expectedSequent, firstOpenGoal);
    }
}
