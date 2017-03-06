package de.uka.ilkd.key.logic;

import java.util.Set;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.AbstractPropositionalExpansionMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.TacletForTests;
import junit.framework.TestCase;


/**
 * Program variables are now introduced locally.
 *
 * These tests check that this is done correctly.
 *
 * @author mulbrich
 * @since 2017-03
 */

public class TestLocalSymbols extends TestCase {

    static class LocalMacro extends AbstractPropositionalExpansionMacro {

        @Override
        public String getName() {
            return "Local strategy for TestLocalSymbols";
        }

        @Override
        public String getDescription() {
            return "n/a";
        }

        @Override
        protected Set<String> getAdmittedRuleNames() {
            return asSet("andRight", "orRight", "forallRight");
        }

        @Override
        protected boolean allowOSS() {
            return false;
        }

    }

    private NoPosTacletApp andRight;
    private NoPosTacletApp orRight;
    private Services services;
    private NoPosTacletApp allRight;

    @Override
    protected void setUp() throws Exception {
        TacletForTests.parse();
        andRight = TacletForTests.getTaclet("and_right");
        allRight = TacletForTests.getTaclet("all_right");
        orRight = TacletForTests.getTaclet("or_right");
        services = TacletForTests.services();
    }

    // Skolem names are the same on two branches and are reset if pruned.
    public void testSkolemization() throws Exception {


        Term target = TacletForTests.parseTerm(
                  "((\\forall s varr; varr=const) | (\\forall s varr; const=varr)) & "
                + "((\\forall s varr; varr=const) | (\\forall s varr; const=varr))");

        Proof proof = new Proof("TestLocalSymbols", target, "n/a", TacletForTests.initConfig());

        apply(proof, andRight, 0, 1);
        apply(proof, orRight, 0, 1);
        apply(proof, allRight, 0, 1);
        apply(proof, allRight, 0, 2);
        apply(proof, orRight, 1, 1);
        apply(proof, allRight, 0, 1);
        apply(proof, allRight, 0, 2);

        for (Goal g : proof.openGoals()) {
            System.out.println(g);
        }

        for (Goal g : proof.openGoals()) {
            String actual = g.sequent().toString();
            assertEquals("[]==>[equals(varr_0,const),equals(const,varr_1)]", actual);
        }

        proof.pruneProof(proof.root());

        apply(proof, andRight, 0, 1);
        apply(proof, orRight, 0, 1);
        apply(proof, allRight, 0, 1);
        apply(proof, allRight, 0, 2);
        apply(proof, orRight, 1, 1);
        apply(proof, allRight, 0, 1);
        apply(proof, allRight, 0, 2);

        for (Goal g : proof.openGoals()) {
            String actual = g.sequent().toString();
            assertEquals("[]==>[equals(varr_0,const),equals(const,varr_1)]", actual);
        }

    }

    private void apply(Proof proof, NoPosTacletApp rule, int goalNo, int formulaNo) {

        ImmutableList<Goal> goals = proof.openGoals();
        while(goalNo > 0) {
            goals = goals.tail();
            goalNo --;
        }

        Goal goal = goals.head();

        TacletApp app;
        PosInOccurrence pio = new PosInOccurrence(goal.node().sequent().getFormulabyNr(formulaNo),
                PosInTerm.getTopLevel(), false);

        app = rule.matchFind(pio, services);
        app = app.setPosInOccurrence(pio , services);
        app = app.tryToInstantiate(services.getOverlay(goal.getLocalNamespaces()));

        goal.apply(app);
    }

}
