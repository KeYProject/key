/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.JPContext;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.nparser.NamespaceBuilder;
import de.uka.ilkd.key.proof.init.JavaProfile;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.junit.jupiter.api.TestInstance;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import static org.junit.jupiter.api.Assertions.assertEquals;

/// Tests for [AlwaysAbnormallyTerminatingAnalysis], i.e. the JLS 14.22 notion of a statement that
/// cannot complete normally.
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class AlwaysAbnormallyTerminatingAnalysisTest {
    private final Services services = new Services(JavaProfile.getDefaultProfile());
    private final JPContext context;

    public AlwaysAbnormallyTerminatingAnalysisTest() {
        NamespaceBuilder nb = new NamespaceBuilder(services.getNamespaces());
        nb.addSort("boolean").addSort("int").addSort("Seq").addSort("LocSet").addSort("double")
                .addSort("float");

        services.activateJava(null);

        var cu = StaticJavaParser.parse("""
                public class Context {
                    boolean x, y, z;
                    int n;
                }
                """);
        services.getJavaService().getSymbolResolver().inject(cu);
        context = new JPContext((ClassOrInterfaceDeclaration) cu.types().getFirst(), cu);
        services.getJavaService().parseSpecialClasses();
    }

    private Statement parseStatement(String javaStatementSource) {
        return (Statement) services.getJavaService()
                .readBlock("{" + javaStatementSource + "}", context, null).program();
    }

    @ParameterizedTest(name = "[{index}] {1}")
    @CsvSource(delimiterString = "~", value = {
        // expectedCannotCompleteNormally ~ description ~ source
        "true  ~ if/else both return                         ~ if (x) { return 1; } else { return 2; }",
        "true  ~ constant true if with returning then      ~ if (true) { return 1; } else { y = z; }",
        "false ~ if/else only then returns                 ~ if (x) { return 1; } else { y = z; }",
        "false ~ if with no else                           ~ if (x) { return 1; }",
        "false ~ if with non-constant or-false guard      ~ if (x || false) { y = z; } else { return 1; }",
        "true  ~ if with always-false and guard            ~ if (x && false) { y = z; } else { return 1; }",
        "false ~ sequence with a conditional return        ~ if (x) { return 1; } y = z;",
        "true  ~ sequence with an unconditional return     ~ if (x) { y = z; } return 1;",
        "false ~ while with non-constant guard             ~ while (x) { return 1; }",
        "true  ~ while(true) with a return                 ~ while (true) { return 1; }",
        "false ~ while(true) with a break                  ~ while (true) { if (x) { break; } return 1; }",
        "true  ~ while(true) without a break               ~ while (true) { y = z; }",
        "true  ~ for(;;) with a return                     ~ for (;;) { return 1; }",
        "false ~ for(;x;) with a return                    ~ for (; x;) { return 1; }",
        "true  ~ do/while with a return                    ~ do { return 1; } while (x);",
        "true  ~ endless do/while                          ~ do { y = z; } while (true);",
        "false ~ do/while(true) with a break               ~ do { if (x) { break; } return 1; } while (true);",
        "false ~ do/while with a reachable continue        ~ do { continue; } while (false);",
        "false ~ do/while with a conditional continue      ~ do { if (x) { continue; } else { return 1; } } while (false);",
        "true  ~ endless do/while with a continue          ~ do { continue; } while (true);",
        "false ~ enhanced for with a return                ~ for (int k : new int[] { 1 }) { return 1; }",
        "false ~ switch without default                    ~ switch (n) { case 1: return 1; }",
        "true  ~ switch with default, all cases return     ~ switch (n) { case 1: return 1; default: throw new RuntimeException(); }",
        "false ~ switch with default and a break           ~ switch (n) { case 1: break; default: return 1; }",
        "true  ~ try/catch that both return                ~ try { return 1; } catch (RuntimeException e) { return 2; }",
        "false ~ try/catch that recovers                   ~ try { throw new RuntimeException(); } catch (RuntimeException e) { y = z; }",
        "true  ~ try/finally where finally always returns  ~ try { y = z; } finally { return 1; }",
        "true  ~ labeled block with a return               ~ label: { return 1; }",
        "false ~ labeled block with a break                ~ label: { break label; }",
        "true  ~ throw                                     ~ throw new RuntimeException();",
        "false ~ plain statement                           ~ y = z;",
        "false ~ assert with a constant-false condition    ~ assert false;",
        "false ~ assert with a constant-true condition     ~ assert true;",
        "false ~ assert with non-constant or-false         ~ assert (x || false);",
        "false ~ assert with always-false and              ~ assert (x && false);",
    })
    void statementCannotCompleteNormally(boolean expected, String description, String source) {
        Statement stmt = parseStatement(source);
        var analysis = new AlwaysAbnormallyTerminatingAnalysis(services);
        assertEquals(expected, analysis.isAlwaysAbnormallyTerminating(stmt), description);
    }
}
