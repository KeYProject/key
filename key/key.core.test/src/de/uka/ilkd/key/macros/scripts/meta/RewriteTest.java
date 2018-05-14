package de.uka.ilkd.key.macros.scripts.meta;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import org.junit.Test;
import java.io.File;
import java.io.IOException;

public class RewriteTest {

    /**
     * Test for finding `f=x` and replacing it with `x=f`
     * Taclet to be found and applied: eqSymm on `f=x`
     */
    @Test
    public void testTransitive() throws IOException, ScriptException, InterruptedException {

        KeYEnvironment<DefaultUserInterfaceControl> env = null;
        try {
            File f = new File("../key.core.test/resources/testcase/scriptCommands/transitive.key");
            // env = KeYEnvironment.load(new File("../key.ui/examples/heap/vstte10_01_SumAndMax/SumAndMax_sumAndMax.key"));
            env = KeYEnvironment.load(f);
        } catch (ProblemLoaderException e) {
            e.printStackTrace();
        }
        Proof proof = env.getLoadedProof();

        //KeY Script
        ProofScriptEngine engine = new ProofScriptEngine(new File("../key.core.test/resources/testcase/scriptCommands/rewrite.script"));

        engine.execute(env.getUi(), proof);
        assert proof.openGoals().take(0).head().sequent().toString().equals("[equals(x,f),equals(x,z)]==>[equals(z,f)]");




    }

    /**
     * Test for finding `f<x` and replacing it with `x>f`
     * Taclet to be found and applied: lt_to_gt on `f>x`
     */
    @Test
    public void testLessTransitive() throws IOException, ScriptException, InterruptedException {

        //File
        KeYEnvironment<DefaultUserInterfaceControl> env = null;
        try {
            File f = new File("../key.core.test/resources/testcase/scriptCommands/less_trans.key");
            env = KeYEnvironment.load(f);
        } catch (ProblemLoaderException e) {
            e.printStackTrace();
        }
        Proof proof = env.getLoadedProof();


        //KeY Script
        ProofScriptEngine engine = new ProofScriptEngine(new File("../key.core.test/resources/testcase/scriptCommands/lesstrans.script"));

        engine.execute(env.getUi(), proof);

        assert proof.openGoals().take(0).head().sequent().toString().equals("[]==>[imp(and(gt(x,f),lt(x,z)),lt(f,z))]");

    }

    /*
    @Test
    public void equality() throws IOException, ScriptException, InterruptedException {

        //File
        KeYEnvironment<DefaultUserInterfaceControl> env = null;
        try {
            File f = new File("../key.core.test/resources/testcase/scriptCommands/eq.key");
            env = KeYEnvironment.load(f);
        } catch (ProblemLoaderException e) {
            e.printStackTrace();
        }
        Proof proof = env.getLoadedProof();


        //KeY Script
        ProofScriptEngine engine = new ProofScriptEngine(new File("../key.core.test/resources/testcase/scriptCommands/eq.script"));

        engine.execute(env.getUi(), proof);


    }
    */
}
