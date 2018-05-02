package de.uka.ilkd.key.macros.scripts.meta;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TestTerm;
import de.uka.ilkd.key.macros.scripts.EngineState;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.macros.scripts.RewriteCommand;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.TestProofStarter;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.IOException;

public class RewriteTest {

    @Test
    public void testTransitive() throws IOException, ScriptException, InterruptedException {

        //File
        KeYEnvironment<DefaultUserInterfaceControl> env = null;
        try {
            File f = new File("../key.core.test/resources/testcase/scriptCommands/transitive.key");
            // env = KeYEnvironment.load(new File("../key.ui/examples/heap/vstte10_01_SumAndMax/SumAndMax_sumAndMax.key"));
            env = KeYEnvironment.load(f);
        } catch (ProblemLoaderException e) {
            e.printStackTrace();
        }
        Proof proof = env.getLoadedProof();
        System.out.println("TestStart:" + proof.openGoals().head().sequent());


        //KeY Script
        ProofScriptEngine engine = new ProofScriptEngine(new File("../key.core.test/src/de/uka/ilkd/key/macros/scripts/meta/rewrite.script"));

        engine.execute(env.getUi(), proof);
        System.out.println("TestEnd_head:" + proof.openGoals().take(0).head().sequent());
        assert proof.openGoals().take(0).head().sequent().toString().equals("[equals(f,x),equals(x,z)]==>[equals(z,f)]");




    }

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
        System.out.println("TestStart:" + proof.openGoals().head().sequent());


        //KeY Script
        ProofScriptEngine engine = new ProofScriptEngine(new File("../key.core.test/src/de/uka/ilkd/key/macros/scripts/meta/lesstrans.script"));

        engine.execute(env.getUi(), proof);

        System.out.println("TestEnd_head:" + proof.openGoals().take(0).head().sequent());
        assert proof.openGoals().take(0).head().sequent().toString().equals("[]==>[imp(and(gt(x,f),lt(x,z)),lt(f,z))]");

    }

    /*
        Test wil fail, rewrite command not yet applicable on subterms
     */
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
        System.out.println("TestStart:" + proof.openGoals().head().sequent());


        //KeY Script
        ProofScriptEngine engine = new ProofScriptEngine(new File("../key.core.test/src/de/uka/ilkd/key/macros/scripts/meta/eq.script"));

        engine.execute(env.getUi(), proof);

        System.out.println("TestEnd_head:" + proof.openGoals().take(0).head().sequent());
        assert proof.openGoals().take(0).head().sequent().toString().equals("[imp(equals(c,c),lt(a,c))]");

    }
}
