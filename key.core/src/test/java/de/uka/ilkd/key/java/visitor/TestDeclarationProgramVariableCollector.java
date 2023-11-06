/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.rule.TacletForTests;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.assertTrue;

public class TestDeclarationProgramVariableCollector {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(TestDeclarationProgramVariableCollector.class);

    // some nonsense java blocks with lots of statements and expressions
    private static final String[] jblocks = new String[] { "{ int j1 = 0; int j2, j3, j4 = 0;}",
        "{ int j1; { int j2; } { int j3; } for (int j4; j4=0; j4++) {} int j5; }",
        "{ int j0; { { { { {  int j1; } int j2; } int j3;} int j4; } } }" };

    // names of variables expected to be collected in jblocks
    private static final String[][] expectedVars =
        new String[][] { { "j1", "j2", "j3", "j4" }, { "j1", "j5" }, { "j0" } };


    private static JavaBlock[] test_block = new JavaBlock[jblocks.length];

    private static int testCases = 0;
    private static int down = 0;

    public TestDeclarationProgramVariableCollector() {
        testCases++;
    }


    @BeforeEach
    public void setUp() {
        if (down != 0) {
            return;
        }
        final Recoder2KeY r2k = new Recoder2KeY(TacletForTests.services(), new NamespaceSet());
        for (int i = 0; i < jblocks.length; i++) {
            test_block[i] = r2k.readBlockWithEmptyContext(jblocks[i]);
        }
    }

    @AfterEach
    public void tearDown() {
        down++;
        if (down < testCases) {
            return;
        }
        test_block = null;
    }

    private HashSet<String> toNames(Set<? extends Named> programVariables) {
        HashSet<String> result = new HashSet<>();
        for (Named programVariable : programVariables) {
            String name = "" + programVariable.name();
            if (result.contains(name)) {
                LOGGER.warn(
                    "Warning: Program variables have same name." + " Probably unsane test case");
            }
            result.add(name);
        }
        return result;
    }


    @Test
    public void testVisitor() {
        DeclarationProgramVariableCollector dpvc;
        for (int i = 0; i < jblocks.length; i++) {
            dpvc = new DeclarationProgramVariableCollector(test_block[i].program(),
                TacletForTests.services());
            dpvc.start();
            HashSet<String> names = toNames(dpvc.result());


            assertTrue(dpvc.result().size() <= expectedVars[i].length, ""
                + "Too many variables collected. Collected:" + dpvc.result() + " in " + jblocks[i]);


            for (int j = 0; j < expectedVars[i].length; j++) {
                assertTrue(names.contains(expectedVars[i][j]),
                    "Missing variable: " + expectedVars[i][j] + " of " + jblocks[i]);
            }
        }
    }

}
