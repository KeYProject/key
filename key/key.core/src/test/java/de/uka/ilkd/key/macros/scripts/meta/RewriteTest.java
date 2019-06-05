package de.uka.ilkd.key.macros.scripts.meta;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;

import java.io.File;
import java.io.IOException;

public class RewriteTest {

    /**
     * Test for finding `f=x` and replacing it with `x=f`
     * Taclet to be found and applied: eqSymm on `f=x`
     */
    @Test
    public void testTransitive() throws IOException, ScriptException, InterruptedException, ProblemLoaderException {
        File script = new File(HelperClassForTests.TESTCASE_DIRECTORY, "scriptCommands/rewrite.script");
        File keyFile = new File(HelperClassForTests.TESTCASE_DIRECTORY, "scriptCommands/transitive.key");

        Assume.assumeTrue("Required script file not found: " + script, script.exists());
        Assume.assumeTrue("Required KeY file not found: " + keyFile, keyFile.exists());

        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        Assert.assertNotNull(env);

        Proof p = env.getLoadedProof();
        ProofScriptEngine engine = new ProofScriptEngine(script);
        engine.execute(env.getUi(), p);

        String firstOpenGoal = p.openGoals().head().sequent().toString();
        String expectedSequent = "[equals(x,f),equals(x,z)]==>[equals(z,f)]";

        Assert.assertEquals(expectedSequent, firstOpenGoal);
    }

    /**
     * Test for finding `f<x` and replacing it with `x>f`
     * Taclet to be found and applied: lt_to_gt on `f>x`
     */
    @Test
    public void testLessTransitive() throws IOException, ScriptException, InterruptedException, ProblemLoaderException {
        File script = new File(HelperClassForTests.TESTCASE_DIRECTORY, "scriptCommands/lesstrans.script");
        File keyFile = new File(HelperClassForTests.TESTCASE_DIRECTORY, "scriptCommands/less_trans.key");

        Assume.assumeTrue("Required script file not found: " + script, script.exists());
        Assume.assumeTrue("Required KeY file not found: " + keyFile, keyFile.exists());

        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(keyFile);
        Proof proof = env.getLoadedProof();
        ProofScriptEngine engine = new ProofScriptEngine(script);
        engine.execute(env.getUi(), proof);

        String firstOpenGoal = proof.openGoals().head().sequent().toString();
        String expectedSequent = "[]==>[imp(and(gt(x,f),lt(x,z)),lt(f,z))]";

        Assert.assertEquals(expectedSequent, firstOpenGoal);
    }
}
