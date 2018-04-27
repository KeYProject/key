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
    public void testRewrite() throws IOException, ScriptException, InterruptedException {

        //File
        KeYEnvironment<DefaultUserInterfaceControl> env = null;
        try {
            env = KeYEnvironment.load(new File("../key.ui/examples/standard_key/prop_log/contraposition.key"));
        } catch (ProblemLoaderException e) {
            e.printStackTrace();
        }
        Proof proof = env.getLoadedProof();
        System.out.println("TestStart:" + proof.openGoals().head().sequent());


        //KeY Script
        ProofScriptEngine engine = new ProofScriptEngine(new File("C:/Users/Lulu/Desktop/Bachelor/key/key/key.core.test/src/de/uka/ilkd/key/macros/scripts/meta/rewrite.script"));

        engine.execute(env.getUi(), proof);
        System.out.println("TestEnd_head:" + proof.openGoals().take(1).head().sequent());




    }


    @Test
    public void testRewrite2() throws IOException, ScriptException, InterruptedException {

        //File
        KeYEnvironment<DefaultUserInterfaceControl> env = null;
        try {
            env = KeYEnvironment.load(new File("C:/Users/Lulu/Desktop/Bachelor/key/key.ui/examples/heap/vstte10_01_SumAndMax/SumAndMax_sumAndMax.key"));
        } catch (ProblemLoaderException e) {
            e.printStackTrace();
        }
        Proof proof = env.getLoadedProof();
        System.out.println("TestStart:" + proof.openGoals().head().sequent());


        //KeY Script
        ProofScriptEngine engine = new ProofScriptEngine(new File("C:/Users/Lulu/Desktop/Bachelor/key/key/key.core.test/src/de/uka/ilkd/key/macros/scripts/meta/rewrite.script"));

        engine.execute(env.getUi(), proof);
        System.out.println("TestEnd_head:" + proof.openGoals().take(1).head().sequent());




    }
}
