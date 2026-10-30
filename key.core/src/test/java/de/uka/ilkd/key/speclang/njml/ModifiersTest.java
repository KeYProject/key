/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.njml;

import java.io.IOException;
import java.net.URISyntaxException;

import de.uka.ilkd.key.java.JavaService;
import de.uka.ilkd.key.java.ast.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.ast.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.rule.TacletForTests;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ModifiersTest {
    private static JavaService java = null;

    @BeforeEach
    public void setUp() throws URISyntaxException, IOException {
        if (java == null) {
            java = TacletForTests.services().getJavaService();
        }
    }

    private static final String CLASSES =
        """
                package test;

                public /*@ nullable_by_default @*/ class A {}

                public /*@ nullable_by_default @*/ class B {}

                public /*@ pure @*/ class C {}
                """;

    private static final String METHODS =
        """
                package test;

                public class D {
                    public /*@ helper @*/ void a() {}

                    /*@ model_behaviour
                      @ requires true;
                      @ static helper model void modelA();
                      @*/

                    public int spacer;

                    public /*@ helper @*/ void b() {}

                    /*@ model_behaviour
                      @ requires true;
                      @ static helper model void modelB();
                      @*/
                }
                """;

    @Test
    public void testClassModifiers() {
        var cu = java.readCompilationUnit(CLASSES);
        var decls = cu.getDeclarations();
        var a = decls.get(0);
        var b = decls.get(1);
        var c = decls.get(2);
        var expected = new TypeDeclaration.JMLModifiers(false, false, true, null);
        assertEquals(expected, a.getJmlModifiers());
        // assertEquals(expected, b.getJmlModifiers());
        assertTrue(c.getJmlModifiers().pure());
    }

    @Test
    public void testMethodModifiers() {
        var cu = java.readCompilationUnit(METHODS);
        var pm = cu.getDeclarations().get(0).getMembers().stream()
                .filter(m -> m instanceof ProgramMethod).map(m -> (ProgramMethod) m).toList();
        var a = pm.get(0).getMethodDeclaration();
        var modelA = pm.get(1).getMethodDeclaration();
        var b = pm.get(2).getMethodDeclaration();
        var modelB = pm.get(3).getMethodDeclaration();
        var expected = new MethodDeclaration.JMLModifiers(false, false, true, null);
        assertEquals(expected, a.getJmlModifiers(), "Jml modifiers of method D::a");
        assertEquals(expected, b.getJmlModifiers(), "Jml modifiers of method D::b");
        assertEquals(expected, modelA.getJmlModifiers(),
            "Jml modifiers of method D::modelA");
        assertEquals(expected, modelB.getJmlModifiers(),
            "Jml modifiers of method D::modelB");
    }
}
