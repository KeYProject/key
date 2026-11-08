/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Arrays;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.operator.TypeCast;
import de.uka.ilkd.key.java.ast.statement.If;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.nparser.NamespaceBuilder;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.junit.jupiter.api.TestInstance;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class BindingsOfExprTest {
    private final Services services = new Services(JavaProfile.getDefaultProfile());
    private final de.uka.ilkd.key.java.ast.JPContext context;

    public BindingsOfExprTest() {
        var nss = services.getNamespaces();
        NamespaceBuilder nb = new NamespaceBuilder(nss);
        nb.addSort("boolean").addSort("int").addSort("Seq").addSort("LocSet").addSort("double")
                .addSort("float");
        services.activateJava(null);

        var cu = StaticJavaParser.parse("""
                public class Context {
                    Object o, o2;
                }
                """);
        services.getJavaService().getSymbolResolver().inject(cu);
        context =
            new de.uka.ilkd.key.java.ast.JPContext(
                (ClassOrInterfaceDeclaration) cu.types().getFirst(), cu);
        services.getJavaService().parseSpecialClasses();
    }

    /**
     * Parses the given condition as the guard of an {@code if} statement and applies the given
     * meta construct to it, returning the names of the introduced pattern variables.
     */
    private String[] apply(String cond, boolean positive) {
        return Arrays.stream(declarations(cond, positive)).map(vs -> vs.getProgramVariable()
                .name().toString()).toArray(String[]::new);
    }

    private VariableSpecification[] declarations(String cond, boolean positive) {
        String block = "{ Object o, o2; if (" + cond + ") { } }";
        StatementBlock sb =
            (StatementBlock) services.getJavaService().readBlock(block, context, null).program();
        If ifStmt = (If) sb.getStatementAt(1);
        Expression guard = ifStmt.getExpressionAt(0);

        ProgramSV sv = SchemaVariableFactory.createProgramSV(
            new ProgramElementName("#nse"), ProgramSVSort.EXPRESSION, false);
        var meta =
            positive ? new PositiveBindingsOfExpr(sv) : new NegativeBindingsOfExpr(sv);
        SVInstantiations inst = SVInstantiations.EMPTY_SVINSTANTIATIONS.add(sv, guard, services);

        return Arrays.stream(meta.transform(null, services, inst))
                .map(pe -> {
                    assertInstanceOf(LocalVariableDeclaration.class, pe);
                    return (LocalVariableDeclaration) pe;
                })
                .map(decl -> decl.getVariableSpecifications().get(0))
                .toArray(VariableSpecification[]::new);
    }

    @ParameterizedTest(name = "positive bindings of [{0}] -> {1}")
    @CsvSource(delimiterString = "|", value = {
        "o instanceof String s                                | s",
        "!(o instanceof String s)                             | ",
        "o instanceof String s && o2 instanceof Object t      | s t",
        "o == null                                            | ",
    })
    void positiveBindings(String cond, String expected) {
        assertArrayEquals(split(expected), apply(cond, true), "positive bindings of: " + cond);
    }

    @ParameterizedTest(name = "negative bindings of [{0}] -> {1}")
    @CsvSource(delimiterString = "|", value = {
        "o instanceof String s                                | ",
        "!(o instanceof String s)                             | s",
        "o instanceof String s || o2 instanceof Object t      | ",
        "o == null                                            | ",
    })
    void negativeBindings(String cond, String expected) {
        assertArrayEquals(split(expected), apply(cond, false), "negative bindings of: " + cond);
    }

    private String[] split(String expected) {
        return expected == null || expected.isBlank() ? new String[0]
                : expected.trim().split("\\s+");
    }

    /** the introduced variables must be declared with a type cast as initializer */
    @ParameterizedTest
    @CsvSource(delimiterString = "|", value = {
        "o instanceof String s           | true",
        "!(o instanceof String s)        | false",
    })
    void declaredWithCast(String cond, boolean positive) {
        VariableSpecification[] specs = declarations(cond, positive);
        assertEquals(1, specs.length);
        assertInstanceOf(TypeCast.class, specs[0].getInitializer());
    }
}
