/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.io.File;
import java.util.Set;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.AbstractPropositionalExpansionMacro;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;


/**
 * Program variables are now introduced locally.
 *
 * These tests check that this is done correctly.
 *
 * @author mulbrich
 * @since 2017-03
 */

public class TestLocalSymbols {
    private static final File TEST_RESOURCES_DIR_PREFIX =
        new File(HelperClassForTests.TESTCASE_DIRECTORY, "localSymbols/");


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

    @BeforeEach
    public void setUp() throws Exception {
        TacletForTests.parse();
        andRight = TacletForTests.getTaclet("and_right");
        allRight = TacletForTests.getTaclet("all_right");
        orRight = TacletForTests.getTaclet("or_right");
        services = TacletForTests.services();
    }

    // Skolem names are the same on two branches and are reset if pruned.
    @Test
    public void testSkolemization() throws Exception {

        Term target = TacletForTests
                .parseTerm("((\\forall s varr; varr=const) | (\\forall s varr; const=varr)) & "
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

    // there was a bug.
    @Test
    public void testDoubleInstantiation() throws Exception {

        KeYEnvironment<?> env = loadProof("doubleSkolem.key");
        Proof proof = env.getLoadedProof();
        String script = env.getProofScript().first;

        ProofScriptEngine pse =
            new ProofScriptEngine(script, new Location(null, Position.newOneBased(1, 1)));
        pse.execute(null, proof);

        ImmutableList<Goal> openGoals = proof.openGoals();
        assert openGoals.size() == 1;
        Goal goal = openGoals.head();
        String actual = goal.sequent().toString();
        assertEquals("[]==>[gt(i_0,Z(0(#))),lt(i_1,Z(0(#)))]", actual);
    }

    private void apply(Proof proof, NoPosTacletApp rule, int goalNo, int formulaNo) {

        ImmutableList<Goal> goals = proof.openGoals();
        while (goalNo > 0) {
            goals = goals.tail();
            goalNo--;
        }

        Goal goal = goals.head();

        TacletApp app;
        PosInOccurrence pio = new PosInOccurrence(goal.node().sequent().getFormulabyNr(formulaNo),
            PosInTerm.getTopLevel(), false);

        app = rule.matchFind(pio, services);
        app = app.setPosInOccurrence(pio, services);
        app = app.tryToInstantiate(services.getOverlay(goal.getLocalNamespaces()));

        goal.apply(app);
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof is not null, and
     * fails if the proof could not be loaded.
     *
     * @param proofFileName The file name of the proof file to load.
     * @return The loaded proof.
     */
    private KeYEnvironment<?> loadProof(String proofFileName) {
        File proofFile = new File(TEST_RESOURCES_DIR_PREFIX, proofFileName);
        Assertions.assertTrue(proofFile.exists(), "Proof file does not exist" + proofFile);

        try {
            KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
                proofFile, null, null, null, true);
            return environment;
        } catch (ProblemLoaderException e) {
            Assertions.fail("Proof could not be loaded.");
            return null;
        }
    }
}
