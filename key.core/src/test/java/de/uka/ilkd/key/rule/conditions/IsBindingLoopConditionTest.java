/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.RuleCollection;
import de.uka.ilkd.key.proof.io.KeYFileForTests;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class IsBindingLoopConditionTest {
    private static final Profile PROFILE = new JavaProfile() {
        @Override
        public RuleCollection getStandardRules() {
            return new RuleCollection(
                org.key_project.util.collection.ImmutableList.of(
                    RuleSourceFactory.fromDefaultLocation(RuleSource.ldtFile),
                    RuleSourceFactory.fromDefaultLocation("javaRules.key")),
                org.key_project.util.collection.ImmutableList.nil());
        }
    };

    private static Services services;
    private static InitConfig initConfig;

    @BeforeAll
    static void setUp() throws Exception {
        var envInput = new KeYFileForTests(
            "IsBindingLoopConditionTest", HelperClassForTests.DUMMY_KEY_FILE, PROFILE);
        initConfig = new ProblemInitializer(PROFILE).prepare(envInput);
        services = initConfig.getServices();
    }

    private static Statement firstStatement(String program) {
        JTerm term = new KeyIO(services, initConfig.namespaces())
                .parseExpression("\\<{" + program + "}\\> true");
        return (Statement) term.javaBlock().program().getFirstElement();
    }

    @Test
    void detectsBindingWhile() {
        assertTrue(IsBindingLoopCondition
                .bindsLoop(firstStatement("while (new String(\"x\") instanceof String s) { }")));
    }

    @Test
    void detectsBindingForAndDo() {
        assertTrue(IsBindingLoopCondition
                .bindsLoop(firstStatement("for (; new String(\"x\") instanceof String s; ) { }")));
        assertTrue(IsBindingLoopCondition
                .bindsLoop(
                    firstStatement("do { } while (new String(\"x\") instanceof String s);")));
    }

    @Test
    void rejectsPlainGuard() {
        assertFalse(IsBindingLoopCondition
                .bindsLoop(firstStatement("while (new String(\"x\") != null) { }")));
    }
}
