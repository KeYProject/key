/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.io.StringReader;
import java.util.List;

import de.uka.ilkd.key.java.loader.JavaParserFactory;
import de.uka.ilkd.key.rule.TacletForTests;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

public class MethodResolutionTest {
    private static final String CLASSES_A = """
            package a;

            public class Super {
                public void test() {}
            }

            public class Derived extends Super {
                // "Overwrites" Super::test, but only when called inside this class
                private void test() {}
            }
            """;

    private static final String CLASSES_B = """
            package b;
            import a.Derived;

            class Caller {
                public void call(Derived d) {
                    // This has to resolve to Super::test
                    // Derived::test is private and not visible from here
                    d.test();
                }
            }
            """;

    public class Super {
        public void test(double d) {}
    }

    public class Derived extends Super {
        // "Overwrites" Super::test, but only when called inside this class
        private void test(int i) {}
    }

    class Caller {
        public void call(Derived d) {
            // This has to resolve to Super::test
            // Derived::test is private and not visible from here
            d.test(1);
        }
    }

    private static JavaParserFactory factory = null;

    @BeforeAll
    public static void init() {
        if (factory == null) {
            var services = TacletForTests.services();
            services.getJavaService().parseSpecialClasses();
            factory = services.getJavaService().getProgramFactory();
        }
    }

    @Test
    public void testShadowingPrivateMethodFromOutsideClass() {
        var cuA =
            factory.parseCompilationUnit(new StringReader(CLASSES_A)).getResult().orElseThrow();
        var cuB =
            factory.parseCompilationUnit(new StringReader(CLASSES_B)).getResult().orElseThrow();
        factory.addUserClasses(List.of(cuA, cuB));
        var superClass = cuA.getClassByName("Super").orElseThrow();
        var derivedClass = cuA.getClassByName("Derived").orElseThrow();
        var callerClass = cuB.getClassByName("Caller").orElseThrow();
        var superTest = superClass.getMethodsByName("test").get(0);
        var callFunction = callerClass.getMethodsByName("call").get(0);
        var paramType = callFunction.getParameter(0).resolve();
        var type = paramType.getType();
        // Method parameter is resolved as 'Derived'
        Assertions.assertSame(
            type.asReferenceType().getTypeDeclaration().orElseThrow().toAst().orElseThrow(),
            derivedClass);
        var callStatement =
            (ExpressionStmt) callFunction.getBody().orElseThrow().getStatements().get(0);
        var methodCallExpr = (MethodCallExpr) callStatement.getExpression();
        var method = methodCallExpr.resolve();
        Assertions.assertEquals(method.accessSpecifier(), AccessSpecifier.PUBLIC);
    }
}
