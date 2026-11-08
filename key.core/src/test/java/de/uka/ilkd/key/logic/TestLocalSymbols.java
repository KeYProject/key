/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Objects;
import java.util.Set;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.AbstractPropositionalExpansionMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;


/**
 * Program variables are now introduced locally.
 * <br>
 * These tests check that this is done correctly.
 *
 * @author mulbrich
 * @since 2017-03
 */
public class TestLocalSymbols {
    private static final Path TEST_RESOURCES_DIR_PREFIX =
        HelperClassForTests.TESTCASE_DIRECTORY.resolve("localSymbols/");


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

        JTerm target = TacletForTests
                .parseTerm("((\\forall s varr; varr=const) | (\\forall s varr; const=varr)) & "
                    + "((\\forall s varr; varr=const) | (\\forall s varr; const=varr))");

        Proof proof = new Proof("TestLocalSymbols", target, null, TacletForTests.initConfig());

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

        proof.pruneProof(Objects.requireNonNull(proof.root(), "a proof always has a root node"));

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
    // the null user interface control in execute is deliberate: the script runs headlessly
    @Test
    @SuppressWarnings("NullAway")
    public void testDoubleInstantiation() throws Exception {
        Path proofFile = TEST_RESOURCES_DIR_PREFIX.resolve("doubleSkolem.key");
        Assertions.assertTrue(Files.exists(proofFile), "Proof file does not exist" + proofFile);

        KeYEnvironment<?> env = KeYEnvironment.load(
            JavaProfile.getDefaultInstance(), proofFile, null, null,
            null, true);

        Proof proof = Objects.requireNonNull(env.getLoadedProof(), "proof must have been loaded");
        var script = Objects.requireNonNull(env.getProofScript(), "proof script must be loaded");

        ProofScriptEngine pse = new ProofScriptEngine(proof);
        pse.execute(null, script);

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
        Sequent sequentFormulas = goal.node().sequent();
        PosInOccurrence pio =
            new PosInOccurrence(sequentFormulas.getFormulaByNr(formulaNo),
                PosInTerm.getTopLevel(), false);

        app = Objects.requireNonNull(rule.matchFind(pio, services),
            "the taclet must match the selected formula");
        app = Objects.requireNonNull(app.setPosInOccurrence(pio, services),
            "setting the occurrence position must succeed");
        app = Objects.requireNonNull(
            app.tryToInstantiate(services.getOverlay(goal.getLocalNamespaces())),
            "instantiation of a matching taclet must succeed");

        goal.apply(app);
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof is not null, and
     * fails if the proof could not be loaded.
     *
     * @param proofFileName The file name of the proof file to load.
     * @return The loaded proof.
     */
    // the catch block always calls Assertions.fail, which does not return; the trailing
    // return null merely satisfies the compiler
    @SuppressWarnings("NullAway")
    private KeYEnvironment<?> loadProof(String proofFileName) {
        Path proofFile = TEST_RESOURCES_DIR_PREFIX.resolve(proofFileName);
        Assertions.assertTrue(Files.exists(proofFile), "Proof file does not exist" + proofFile);

        try {
            return KeYEnvironment.load(JavaProfile.getDefaultInstance(),
                proofFile, null, null, null, true);
        } catch (ProblemLoaderException e) {
            Assertions.fail("Proof could not be loaded.");
            return null;
        }
    }
}
