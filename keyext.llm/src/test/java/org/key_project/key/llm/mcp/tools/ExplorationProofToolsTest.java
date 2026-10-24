/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.tools;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Map;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.SequentFormula;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Functional smoke tests for the exploration machinery behind {@code explore_*} / the
 * {@code probe_*} and {@code explorative_*} tool family, driven on a real loaded proof.
 * <p>
 * The {@code explorative_*} tools rewrite the MAIN proof via cut + hidden occurrence + disabling
 * the other cut branch (the exploration-mode recipe); the {@code probe_*} tools run the auto
 * strategy on an isolated side proof and report whether the goal would close. The tools
 * themselves resolve proofs through the GUI mediator, so these tests call the headless
 * machinery seams directly ({@code applyCutEdit}, {@code runSideProof},
 * {@code buildAddSequent}/{@code buildEditSequent}) on the goal of the loaded problem
 * {@code p() ==> p()}.
 */
class ExplorationProofToolsTest {

    private Path location;
    private KeYEnvironment<?> env;
    private Proof proof;

    @BeforeEach
    void setup() throws ProblemLoaderException {
        location = Paths.get("src/test/resources/org/key_project/key/llm/mcp/tools/explore.key");
        Assumptions.assumeTrue(Files.exists(location), "File explore.key not found.");
        env = KeYEnvironment.load(location);
        proof = env.getLoadedProof();
    }

    @AfterEach
    void tearDown() {
        if (env != null) {
            env.dispose();
        }
        env = null;
        proof = null;
        location = null;
    }

    private Goal goal() {
        return proof.openGoals().iterator().next();
    }

    private JTerm term(String text) throws Exception {
        return new KeyIO(env.getServices(), goal().getLocalNamespaces()).parseExpression(text);
    }

    private static boolean has(Semisequent side, String text, Goal g, KeYEnvironment<?> e)
            throws Exception {
        JTerm t = new KeyIO(e.getServices(), g.getLocalNamespaces()).parseExpression(text);
        for (SequentFormula sf : side) {
            if (sf.formula().equals(t)) {
                return true;
            }
        }
        return false;
    }

    @Test
    void explorativeAddKeepsTheAssumptionBranchAndDisablesTheOther() throws Exception {
        var result = ExploreProofTools.applyCutEdit("test", goal(), proof, proof.getServices(),
            null, term("q()"), true, "added \"q()\"");
        assertTrue(result.startsWith("test:"), result);
        assertEquals(2, proof.openGoals().size(), "the cut produces two goals");
        assertEquals(1, proof.openGoals().stream().filter(g -> !g.isAutomatic()).count(),
            "exactly one cut branch is disabled");
        Goal kept = proof.openGoals().stream().filter(Goal::isAutomatic).findFirst().orElseThrow();
        assertTrue(has(kept.sequent().antecedent(), "q()", kept, env),
            "the kept branch carries the added assumption");
    }

    @Test
    void explorativeEditReplacesTheOldFormulaAndHidesIt() throws Exception {
        var result = ExploreProofTools.applyCutEdit("test", goal(), proof, proof.getServices(),
            term("p()"), term("r()"), true, "replaced \"p()\" by \"r()\"");
        assertTrue(result.startsWith("test:"), result);
        assertEquals(2, proof.openGoals().size());
        assertEquals(1, proof.openGoals().stream().filter(g -> !g.isAutomatic()).count());
        Goal kept = proof.openGoals().stream().filter(Goal::isAutomatic).findFirst().orElseThrow();
        assertTrue(has(kept.sequent().antecedent(), "r()", kept, env),
            "the kept branch carries the replacement");
        assertFalse(has(kept.sequent().antecedent(), "p()", kept, env),
            "the old occurrence is hidden on the kept branch");
        assertTrue(has(kept.sequent().succedent(), "p()", kept, env),
            "the succedent of the kept branch is untouched");
    }

    @Test
    void probeAddFormulaReportsTheBranchClosable() throws Exception {
        var side = ExploreProofTools.buildAddSequent(goal(), term("q()"), true);
        var result = ExploreProofTools.runSideProof("test", Map.of("steps", 200), proof, side,
            true, "with \"q()\" added to the ");
        assertTrue(result.contains("TRUE"), result);
        assertTrue(result.contains("the main proof is unchanged"), result);
        assertEquals(1, proof.openGoals().size(), "the main proof is not touched by a probe");
    }

    @Test
    void probeEditFormulaReportsTheBranchNotClosable() throws Exception {
        var side = ExploreProofTools.buildEditSequent(goal(), term("p()"), term("r()"), true);
        var result = ExploreProofTools.runSideProof("test", Map.of("steps", 200), proof, side,
            true, "after replacing \"p()\" by \"r()\" on the ");
        assertTrue(result.contains("does NOT close"), result);
        assertTrue(result.contains("the main proof is unchanged"), result);
        assertEquals(1, proof.openGoals().size(), "the main proof is not touched by a probe");
    }
}
