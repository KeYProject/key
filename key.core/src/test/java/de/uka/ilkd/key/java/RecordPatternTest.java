/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.io.ProofSaver;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the conversion and the rule decomposition of record patterns
 * ({@code o instanceof Record(int x, ...)}).
 */
class RecordPatternTest {

    private static final Map<String, String> SOURCES = Map.of(
        "RecPatterns", "public class RecPatterns { }\n",
        "Point", "record Point(int x, int y) { }\n",
        "Box", "record Box(Object o) { }\n",
        "Line", "record Line(Point a, int b) { }\n");

    @TempDir
    static Path tempDir;

    private static KeYEnvironment<?> environment;
    private static Services services;
    private static KeyIO keyIO;
    private static TacletIndex rules;

    @BeforeAll
    static void load() throws Exception {
        Path src = tempDir.resolve("src");
        Files.createDirectories(src);
        for (var entry : SOURCES.entrySet()) {
            Files.writeString(src.resolve(entry.getKey() + ".java"), entry.getValue());
        }
        Path problem = tempDir.resolve("problem.key");
        Files.writeString(problem, "\\javaSource \"src\";\n\\problem { true }\n");
        environment = KeYEnvironment.load(problem);
        services = environment.getServices();
        keyIO = new KeyIO(services, environment.getInitConfig().namespaces());
        rules = environment.getInitConfig().createTacletIndex();
    }

    @AfterAll
    static void dispose() {
        if (environment != null) {
            environment.dispose();
        }
    }

    private static JTerm parseTerm(String expression) {
        return keyIO.parseExpression(expression);
    }

    private Goal createGoal(String program) {
        return createGoal(program, rules);
    }

    private Goal createGoal(String program, TacletIndex tacletIndex) {
        var succ =
            ImmutableList.singleton(new SequentFormula(parseTerm("\\<{" + program + "}\\> true")));
        var sequent = JavaDLSequentKit.createSequent(ImmutableList.nil(), succ);
        var proof = new Proof("RecordPatternTest", environment.getInitConfig().deepCopy());
        proof.setRoot(new Node(proof, sequent));
        return new Goal(proof.root(), tacletIndex, new BuiltInRuleAppIndex(new BuiltInRuleIndex()),
            proof.getServices());
    }

    private static PosInOccurrence topLevelPosition(Goal goal) {
        return new PosInOccurrence(goal.sequent().succedent().getFirst(), PosInTerm.getTopLevel(),
            false);
    }

    @Test
    void recordPatternIsConverted() {
        JTerm term = parseTerm(
            "\\<{ Object o = null; if (o instanceof Point(int x, int y)) { int z = x + y; } }\\> true");
        String printed = ProofSaver.printAnything(term, services);
        assertTrue(printed.contains("instanceof Point(int x, int y)"),
            "record pattern should be kept in the program AST, but was:\n" + printed);
    }

}
