/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.JPContext;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.loader.JP2KeYConverter;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.nparser.NamespaceBuilder;
import de.uka.ilkd.key.proof.init.JavaProfile;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.sv.SchemaVariable;

import com.github.javaparser.JavaParser;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.junit.jupiter.api.TestInstance;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * NOTE ON PACKAGE PLACEMENT: put this file in the same package as
 * AlwaysAbnormallyTerminatingAnalysis (it relies on package-private / private
 * access to the record and to the and()/or() helpers via reflection, so it
 * doesn't need any source changes to the class under test).
 * <p>
 * NOTE ON TIER B (statement-level tests): those need a real Services +
 * parsed Statement, which is project-specific plumbing I don't have visibility
 * into. `parseStatement(String)` below is a stub — wire it up to however your
 * test suite already builds a Services/ExecutionContext and parses a method
 * body (KeY 3.x parses via JavaParser under the hood). Everything else in
 * this file works standalone.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class AlwaysAbnormallyTerminatingAnalysisTest {
    private final Services services = new Services(JavaProfile.getDefaultProfile());
    private final JPContext context;
    private final JP2KeYConverter converter;
    private final JavaParser javaParser;
    private final ExecutionContext executionContext;


    // --- plumbing you need to fill in for your project -----------------

    private AlwaysAbnormallyTerminatingAnalysis newAnalysis() {
        return new AlwaysAbnormallyTerminatingAnalysis(executionContext, services);
    }

    private Statement parseStatement(String javaStatementSource) {
        return (Statement) services.getJavaService()
                .readBlock("{" + javaStatementSource + "}", context, null).program();
    }

    public AlwaysAbnormallyTerminatingAnalysisTest() {
        System.out.println("TEST INIT");
        var nss = services.getNamespaces();
        NamespaceBuilder nb = new NamespaceBuilder(nss);
        nb.addSort("boolean").addSort("int").addSort("Seq").addSort("LocSet").addSort("double")
                .addSort("float");

        Namespace<SchemaVariable> nsSchema = new Namespace<>();
        nsSchema.add(SchemaVariableFactory.createProgramSV(
            new ProgramElementName("#a"), ProgramSVSort.EXPRESSION, false));
        nsSchema.add(SchemaVariableFactory.createProgramSV(
            new ProgramElementName("#b"), ProgramSVSort.EXPRESSION, false));
        nsSchema.add(SchemaVariableFactory.createProgramSV(
            new ProgramElementName("#c"), ProgramSVSort.EXPRESSION, false));

        services.activateJava(null);


        var cu = StaticJavaParser.parse("""
                public class Context {
                    boolean x, y, z;
                }
                """);
        services.getJavaService().getSymbolResolver().inject(cu);
        context = new JPContext((ClassOrInterfaceDeclaration) cu.types().getFirst(), cu);
        services.getJavaService().parseSpecialClasses();
        converter = services.getJavaService().getConverter(nsSchema);
        javaParser = services.getJavaService().getProgramFactory().createJavaParser();

        executionContext = new ExecutionContext(
            new TypeRef(new KeYJavaType(PrimitiveType.JAVA_BYTE, new SortImpl(new Name("byte")))),
            null, new LocationVariable(new ProgramElementName("testVar"),
                new SortImpl(new Name("testSort"))));
    }

    @ParameterizedTest(name = "[{index}] {1}")
    @CsvSource(delimiterString = "|", value = {
        // expectedAlwaysAbnormal | description | source
        "true  | if/else both return                   | if (x) { return 1; } else { return 2; }",
        "true | if/else only then returns              | if (true) { return 1; } else { doStuff(); }",
        "false | if/else only then returns             | if (x) { return 1; } else { doStuff(); }",
        "false | if with no else                       | if (x) { return 1; }",
        "true | while(true) with a break              | while (true) { if (x) { break; } return 1; }",
        "false | while(true) with no break at all      | while (true) { doStuff(); }",
        "false | switch without default                | switch (x) { case 1: return 1; }",
        "true  | switch with default, all cases return | switch (x) { case 1: return 1; default: throw new RuntimeException(); }",
        "false | try/catch that recovers                  | try { throw new RuntimeException(); } catch (RuntimeException e) { doStuff(); }",
        "true  | try/finally where finally always returns | try { doStuff(); } finally { return 1; }",
        "true  | assert with a constant-false condition   | assert false;",
        "false | assert with a constant-true condition    | assert true;",
    })
    void statementAlwaysAbnormal(boolean expected, String description, String source) {
        Statement stmt = parseStatement(source);
        AlwaysAbnormallyTerminatingAnalysis analysis = newAnalysis();
        Object result = analysis.abnormallyTerminating(stmt);
        boolean actual = result != null; // TerminationReason#isAbnormallTerminating() should also
                                         // be checked once record fields are trustworthy
        assertEquals(expected, actual, description);
    }
}
