/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.RuleCollection;
import de.uka.ilkd.key.proof.io.KeYFileForTests;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class BindingExpressionCondTest {
    private static final Profile PROFILE = new JavaProfile() {
        @Override
        public RuleCollection getStandardRules() {
            return new RuleCollection(
                ImmutableList.of(
                    RuleSourceFactory.fromDefaultLocation(RuleSource.ldtFile),
                    RuleSourceFactory.fromDefaultLocation("javaRules.key")),
                ImmutableList.nil());
        }
    };

    private static Services services;
    private static InitConfig initConfig;

    @BeforeAll
    static void setUp() throws Exception {
        var envInput = new KeYFileForTests(
            "BindingExpressionCondTest", HelperClassForTests.DUMMY_KEY_FILE, PROFILE);
        initConfig = new ProblemInitializer(PROFILE).prepare(envInput);
        services = initConfig.getServices();
    }

    private static Statement firstStatement(String program) {
        JTerm term = new KeyIO(services, initConfig.namespaces())
                .parseExpression("\\<{" + program + "}\\> true");
        return (Statement) term.javaBlock().program().getFirstElement();
    }

    private static boolean isBinding(Object instantiation, boolean list) {
        ProgramSV sv = SchemaVariableFactory.createProgramSV(
            new ProgramElementName("candidate"), ProgramSVSort.STATEMENT, list);
        SVInstantiations instantiations;
        if (list) {
            instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS.add(
                sv, (ImmutableList<Statement>) instantiation, Statement.class, services);
        } else {
            instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS.add(
                sv, (SyntaxElement) instantiation, services);
        }
        var matchCond = MatchConditions.EMPTY_MATCHCONDITIONS
                .setInstantiations(instantiations);
        SyntaxElement candidate = list ? null : (SyntaxElement) instantiation;
        return new BindingExpressionCond(sv, false)
                .check(sv, candidate, matchCond, services) != null;
    }

    @Test
    void acceptsLoopStatements() {
        assertTrue(isBinding(firstStatement(
            "while (new String(\"x\") instanceof String s) { }"), false));
        assertTrue(isBinding(firstStatement(
            "for (; new String(\"x\") instanceof String s; ) { }"), false));
        assertTrue(isBinding(firstStatement(
            "do { } while (new String(\"x\") instanceof String s);"), false));
    }

    @Test
    void rejectsPlainLoop() {
        assertFalse(isBinding(firstStatement(
            "while (new String(\"x\") != null) { }"), false));
    }

    @Test
    void acceptsStatementListWithBindingLoop() {
        var list = ImmutableList.of(
            firstStatement("int x = 0;"),
            firstStatement("while (new String(\"x\") instanceof String s) { }"));
        assertTrue(isBinding(list, true));
    }

    @Test
    void rejectsStatementListWithoutBindingLoop() {
        var list = ImmutableList.of(
            firstStatement("int x = 0;"),
            firstStatement("while (new String(\"x\") != null) { }"));
        assertFalse(isBinding(list, true));
    }
}
