/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.fixedbugs;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.ServiceConfiguration;
import recoder.abstraction.Type;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.FieldDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.expression.Assignment;
import recoder.java.reference.TypeReference;
import recoder.kit.TypeKit;

/**
 * @author Tobias Gutzmann created on 19.10.2007
 */
public class FixedBugs {
    @Test
    public void testConstructorStartPosition() throws ParserException {
        ServiceConfiguration sc = new CrossReferenceServiceConfiguration();
        ProgramFactory f = sc.getProgramFactory();
        CompilationUnit cu = f.parseCompilationUnit(
            """
                    public class Test
                    {
                    Test s;
                    public Test(Test s)
                    {
                    this.s = s;
                    }
                    }""");
        sc.getChangeHistory().attached(cu);
        Assertions.assertEquals(4, ((ConstructorDeclaration) sc.getNameInfo().getClassType("Test")
                .getConstructors().get(0)).getStartPosition().getLine());

    }

    /**
     * Test for absence of a bug in PrettyPrinter that, after transformation, may mess up single
     * line comments. Bug reported and testcase submitted by M.Ullbrich
     */
    @Test
    public void testComments() throws ParserException {
        ServiceConfiguration sc = new CrossReferenceServiceConfiguration();
        ProgramFactory f = sc.getProgramFactory();
        CompilationUnit cu =
            f.parseCompilationUnit("""
                    class A {


                    //some comment\r
                    A a; } class B {}""");
        sc.getChangeHistory().attached(cu);
        FieldDeclaration fd = (FieldDeclaration) cu.getDeclarations().get(0).getMembers().get(0);
        TypeReference oldType = fd.getTypeReference();
        TypeReference newType = TypeKit.createTypeReference(sc.getProgramFactory(), "B");
        fd.replaceChild(oldType, newType);
        sc.getChangeHistory().replaced(oldType, newType);
        String s = cu.toSource().replaceAll(" ", "");
        Assertions.assertEquals("classA{\n\n\n//somecomment\nBa;\n}classB{\n}\n", s);
    }

    /**
     * Test for implemented generic type argument resolving in field references
     */
    @Test
    public void testFieldTypes() throws ParserException {
        CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
        ProgramFactory f = sc.getProgramFactory();

        CompilationUnit cu = f.parseCompilationUnit(
            "class B { } class G<E> { E field;   void m() { B b; b = new G<B>().field; } }");
        sc.getChangeHistory().attached(cu);
        sc.getChangeHistory().updateModel();

        ClassDeclaration classB = (ClassDeclaration) cu.getDeclarations().get(0);
        ClassDeclaration classG = (ClassDeclaration) cu.getDeclarations().get(1);
        MethodDeclaration methodM = (MethodDeclaration) classG.getMethods().get(0);
        Assignment assignment = (Assignment) methodM.getBody().getChildAt(1);
        Expression rhs = (Expression) assignment.getChildAt(1);
        Type rhsType = sc.getSourceInfo().getType(rhs);

        Assertions.assertEquals(rhsType, classB);
    }

    @Test
    public void testBasicReflectionImport() {
        // make sure non-public fields can be read...
        // weigl, 2023-03-11, disabled, not working under Java 17
        // ReflectionImport.getClassFile("java.lang.String");
    }

    @Test
    public void testIncorrectFileEnd() {
        CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
        ProgramFactory f = sc.getProgramFactory();
        StringBuilder cuText = new StringBuilder("class B { }//");
        cuText.append(" ".repeat(4081));
        for (int i = 4081; i < 4087; i++) {
            // that's around the critical part, where the
            // size of the CU matches the JavaCCParser buffer
            try {
                f.parseCompilationUnit(cuText.toString());
                cuText.append(" ");
            } catch (ParserException pe) {
                Assertions.fail();
            }
        }
    }
}
