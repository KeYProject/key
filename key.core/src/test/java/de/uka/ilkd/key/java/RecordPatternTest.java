/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
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

    private List<String> applicableRules(String program) {
        Goal goal = createGoal(program);
        List<String> names = new ArrayList<>();
        for (TacletApp app : goal.ruleAppIndex()
                .getTacletAppAt(TacletFilter.TRUE, topLevelPosition(goal), services)) {
            names.add(app.taclet().name().toString());
        }
        return names;
    }

    private Goal applyRule(String ruleName, String program) {
        var taclet = rules.lookup(ruleName);
        assertNotNull(taclet, "rule " + ruleName + " not found");
        var tacletIndex = TacletIndexKit.getKit().createTacletIndex();
        tacletIndex.add(taclet);
        Goal goal = createGoal(program, tacletIndex);

        var pos = topLevelPosition(goal);
        var apps = goal.ruleAppIndex().getTacletAppAt(TacletFilter.TRUE, pos, services);
        assertEquals(1, apps.size(),
            "Expected exactly one application of " + ruleName + " at " + pos + ", but found:\n"
                + apps);
        var app = apps.head().tryToInstantiate(services);
        assertNotNull(app, "Rule application of " + ruleName + " could not be completed");
        assertTrue(app.complete(), "Rule application of " + ruleName + " should be complete");

        ImmutableList<Goal> goals = app.taclet().getExecutor().apply(goal, app);
        assertEquals(1, goals.size(), "Applying " + ruleName + " should create a single goal");
        return goals.head();
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

    private static void assertSuccedent(Goal goal, String expectedFormula) {
        JTerm actual = (JTerm) goal.sequent().succedent().getFirst().formula();
        JTerm expected = parseTerm(expectedFormula);
        assertTrue(RENAMING_TERM_PROPERTY.equalsModThisProperty(actual, expected),
            "Expected succedent:\n" + ProofSaver.printAnything(expected, services)
                + "\nBut was:\n" + ProofSaver.printAnything(actual, services));
    }

    @Test
    void recordPatternIsConverted() {
        JTerm term = parseTerm(
            "\\<{ Object o = null; if (o instanceof Point(int x, int y)) { int z = x + y; } }\\> true");
        String printed = ProofSaver.printAnything(term, services);
        assertTrue(printed.contains("instanceof Point(int x, int y)"),
            "record pattern should be kept in the program AST, but was:\n" + printed);
    }

    @Test
    void ifUnfoldPatternDeclaresRecordComponents() {
        Goal goal = applyRule("ifUnfoldPattern",
            "if (new Object() instanceof Point(int x, int y)) { int z = x + y; }");
        assertSuccedent(goal,
            "\\<{boolean b; { b = new Object() instanceof Point; }"
                + " if (b) { int x = ((Point) new Object()).x(); int y = ((Point) new Object()).y();"
                + " int z = x + y; }}\\> true");
    }

    @Test
    void ifUnfoldPatternChecksConditionalComponent() {
        Goal goal = applyRule("ifUnfoldPattern",
            "if (new Object() instanceof Box(String s)) { int z = s.length(); }");
        assertSuccedent(goal,
            "\\<{boolean b;"
                + " { b = new Object() instanceof Box && ((Box) new Object()).o() instanceof String; }"
                + " if (b) { java.lang.String s = (String) ((Box) new Object()).o();"
                + " int z = s.length(); }}\\> true");
    }

    @Test
    void ifUnfoldPatternDoesNotCheckUnconditionalComponent() {
        Goal goal = applyRule("ifUnfoldPattern",
            "if (new Object() instanceof Box(Object v)) { int z = 1; }");
        assertSuccedent(goal,
            "\\<{boolean b; { b = new Object() instanceof Box; }"
                + " if (b) { java.lang.Object v = ((Box) new Object()).o(); int z = 1; }}\\> true");
    }

    @Test
    void ifUnfoldPatternSupportsVarAndMatchAll() {
        Goal goal = applyRule("ifUnfoldPattern",
            "if (new Object() instanceof Point(_, _)) { int z = 1; }");
        assertSuccedent(goal,
            "\\<{boolean b; { b = new Object() instanceof Point; }"
                + " if (b) { int z = 1; }}\\> true");
    }

    @Test
    void ifUnfoldPatternDestructuresNestedRecordPattern() {
        Goal goal = applyRule("ifUnfoldPattern",
            "if (new Object() instanceof Line(Point(int x, int y), int b))"
                + " { int z = x + y; }");
        assertSuccedent(goal,
            "\\<{boolean b;"
                + " { b = new Object() instanceof Line && ((Line) new Object()).a() instanceof Point; }"
                + " if (b) { int x = ((Point) ((Line) new Object()).a()).x();"
                + " int y = ((Point) ((Line) new Object()).a()).y();"
                + " int b = ((Line) new Object()).b(); int z = x + y; }}\\> true");
    }

    @Test
    void ifUnfoldPatternHandlesNegatedRecordPatternInElse() {
        Goal goal = applyRule("ifElseUnfoldPattern",
            "if (!(new Object() instanceof Point(int x, int y))) { int a = 1; }"
                + " else { int z = x + y; }");
        assertSuccedent(goal,
            "\\<{boolean b; { b = !(new Object() instanceof Point); }"
                + " if (b) { int a = 1; } else { int x = ((Point) new Object()).x();"
                + " int y = ((Point) new Object()).y(); int z = x + y; }}\\> true");
    }

    @Test
    void recordPatternIsSelectedForIf() {
        List<String> names =
            applicableRules("if (new Object() instanceof Point(int x, int y)) { }");
        assertTrue(names.contains("ifUnfoldPattern"), "ifUnfoldPattern should apply: " + names);
        assertFalse(names.contains("ifUnfold"), "ifUnfold must not apply: " + names);
    }

    @Test
    void recordPatternAssignmentIsLowered() {
        Goal goal = applyRule("recordPatternAssignment",
            "boolean c = new Object() instanceof Point(int x, int y);");
        assertSuccedent(goal,
            "\\<{boolean c = new Object() instanceof Point;}\\> true");
    }

    @Test
    void recordPatternAssignmentChecksConditionalComponent() {
        Goal goal = applyRule("recordPatternAssignment",
            "boolean c = new Object() instanceof Box(String s);");
        assertSuccedent(goal,
            "\\<{boolean c = new Object() instanceof Box"
                + " && ((Box) new Object()).o() instanceof String;}\\> true");
    }
}
