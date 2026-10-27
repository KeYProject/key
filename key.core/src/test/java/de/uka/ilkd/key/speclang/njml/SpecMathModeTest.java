/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.JavaService;
import de.uka.ilkd.key.java.ast.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.rule.TacletForTests;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Tests that the {@code spec_*_math} JML pragmas reach the spec math mode of the converted
 * KeY declarations. JMLtk parses them as JML modifiers (class level, method level, and inline
 * in model method declarations); the conversion must map them to the {@code ModifierKind}
 * {@code JML_SPEC_*} constants so that {@code JMLInfoExtractor} picks them up. Silently dropping
 * a pragma would silently change the math of every translated term.
 */
public class SpecMathModeTest {
    private static JavaService java = null;

    @BeforeEach
    public void setUp() {
        if (java == null) {
            java = TacletForTests.services().getJavaService();
        }
    }

    private static final String TARGET =
        """
                package test;

                /*@ spec_java_math @*/
                public class MathHolder {

                    /*@ model_behaviour
                      @ requires true;
                      @ static spec_bigint_math model boolean abs(\\bigint v);
                      @*/

                    public int spacer;

                    public /*@ spec_bigint_math @*/ void big() {}

                    /*@ spec_safe_math @*/ public void safe() {}

                    public void plain() {}

                    /*@ model_behaviour
                      @ requires true;
                      @ static model boolean mod(int v);
                      @*/
                    public int spacer2;
                }
                """;

    @Test
    public void testSpecMathModes() {
        var cu = java.readCompilationUnit(TARGET);
        TypeDeclaration td = cu.getDeclarations().get(0);
        assertEquals(SpecMathMode.JAVA, td.getJmlModifiers().specMathMode(),
            "class-level spec_java_math pragma must set the type's spec math mode");

        var methods = td.getMembers().stream().filter(m -> m instanceof ProgramMethod)
                .map(m -> (ProgramMethod) m).toList();
        // getMembers may contain compiler artifacts (e.g. implicit constructors); match by name.
        assertEquals(SpecMathMode.BIGINT, modeOf(methods, "big"),
            "method-level spec_bigint_math modifier must set BIGINT");
        assertEquals(SpecMathMode.SAFE, modeOf(methods, "safe"),
            "method-level spec_safe_math modifier must set SAFE");
        assertNull(modeOf(methods, "plain"),
            "method without pragma must not invent a mode (inherits from class)");
    }

    private static SpecMathMode modeOf(java.util.List<ProgramMethod> methods, String name) {
        return methods.stream().filter(m -> m.getName().equals(name)).findFirst()
                .orElseThrow(() -> new AssertionError("no method " + name))
                .getMethodDeclaration().getJmlModifiers().specMathMode();
    }

    @Test
    public void testModelMethodInlineMathMode() {
        var cu = java.readCompilationUnit(TARGET);
        var pm = cu.getDeclarations().get(0).getMembers().stream()
                .filter(m -> m instanceof ProgramMethod)
                .map(m -> (ProgramMethod) m)
                .filter(m -> m.getName().equals("abs"))
                .findFirst().orElseThrow(() -> new AssertionError("no model method abs"));
        // The model method declaration carries the inline `spec_bigint_math` modifier that JMLtk
        // parsed inside the model contract; it must survive onto the converted method.
        assertEquals(SpecMathMode.BIGINT,
            pm.getMethodDeclaration().getJmlModifiers().specMathMode());
    }
}
