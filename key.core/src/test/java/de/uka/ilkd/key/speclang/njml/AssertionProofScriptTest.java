/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.njml;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.JavaService;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.statement.JmlAssert;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement.Kind;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests that JML assertion proof scripts (`assert e \by { ... }`) survive the JMLtk front-end:
 * {@code JP2KeYConverter} must turn the JMLtk proof nodes back into KeY's own
 * {@link de.uka.ilkd.key.nparser.KeyAst.JMLProofScript} instead of silently dropping them.
 */
public class AssertionProofScriptTest {

    private static JavaService java = null;

    @BeforeEach
    public void setUp() {
        if (java == null) {
            java = TacletForTests.services().getJavaService();
        }
    }

    private static final String TARGET =
        """
                public class ScriptHolder {
                    int x;

                    void m() {
                        //@ assert x > 0 \\by { auto; };
                        //@ assume x <= 0;
                        //@ assert x != 0;
                    }
                }
                """;

    @Test
    public void testProofScriptIsRetained() {
        var cu = java.readCompilationUnit(TARGET);
        var member = cu.getDeclarations().get(0).getMembers().stream()
                .filter(m -> m instanceof ProgramMethod)
                .map(m -> (ProgramMethod) m)
                .findFirst().orElseThrow();
        List<JmlAssert> asserts = new ArrayList<>();
        collectAsserts(member.getMethodDeclaration().getBody(), asserts);

        assertEquals(3, asserts.size(),
            "assert and assume statements must be converted to JmlAssert");
        JmlAssert withScript = asserts.get(0);
        JmlAssert assume = asserts.get(1);
        JmlAssert withoutScript = asserts.get(2);
        assertEquals(Kind.ASSERT, withScript.getKind());
        assertEquals(Kind.ASSUME, assume.getKind());
        assertNotNull(withScript.getAssertionProof(),
            "assert e \\by { auto; } must keep its proof script");
        assertNull(withoutScript.getAssertionProof(),
            "assert without \\by must not invent a script");
        assertNull(assume.getAssertionProof(),
            "assume without \\by must not invent a script");
        assertTrue(withScript.getAssertionProof().collectTerms() != null,
            "proof script must be re-parseable into KeY terms");
    }

    private static void collectAsserts(Statement statement, List<JmlAssert> out) {
        if (statement instanceof JmlAssert jmlAssert) {
            out.add(jmlAssert);
        } else if (statement instanceof StatementBlock block) {
            for (var child : block.getBody()) {
                collectAsserts(child, out);
            }
        }
    }
}
