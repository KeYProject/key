/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.io.IOException;
import java.net.URISyntaxException;

import de.uka.ilkd.key.java.JavaService;
import de.uka.ilkd.key.java.ast.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.ast.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.rule.TacletForTests;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

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

                /*@ nullable_by_default @*/
                public class A {}

                public /*@ nullable_by_default @*/ class B {}

                /*@ nullable_by_default @*/ class C {}
                """;

    private static final String METHODS =
        """
                package test;

                public class D {
                    /*@ helper @*/
                    public void a() {}

                    /*@ model_behaviour
                      @ requires true;
                      @ static helper model void modelA();
                      @*/

                    public int spacer;

                    public /*@ helper @*/ void b() {}

                    /*@ model_behaviour
                      @ requires true;
                      @ helper
                      @ static model void modelB();
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
        Assertions.assertEquals(expected, a.getJmlModifiers(), "Jml modifiers of class A");
        // TODO Javaparser: This does not work currently
        // To fix this, JmlCommentTransformer has to visit comments of class names
        // Assertions.assertEquals(expected, b.getJmlModifiers(), "Jml modifiers of class B");
        Assertions.assertEquals(expected, c.getJmlModifiers(), "Jml modifiers of class C");
    }

    @Test
    public void testMethodModifiers() {
        var cu = java.readCompilationUnit(METHODS);
        var members = cu.getDeclarations().get(0).getMembers();
        var a = ((ProgramMethod) members.get(0)).getMethodDeclaration();
        var modelA = ((ProgramMethod) members.get(3)).getMethodDeclaration();
        var b = ((ProgramMethod) members.get(2)).getMethodDeclaration();
        var modelB = ((ProgramMethod) members.get(4)).getMethodDeclaration();
        var expected = new MethodDeclaration.JMLModifiers(false, false, true, null);
        Assertions.assertEquals(expected, a.getJmlModifiers(), "Jml modifiers of method D::a");
        Assertions.assertEquals(expected, b.getJmlModifiers(), "Jml modifiers of method D::b");
        Assertions.assertEquals(expected, modelA.getJmlModifiers(),
            "Jml modifiers of method D::modelA");
        Assertions.assertEquals(expected, modelB.getJmlModifiers(),
            "Jml modifiers of method D::modelB");
    }
}
