/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.njml;

import java.util.HashMap;
import java.util.List;

import de.uka.ilkd.key.java.JavaService;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.jml.translation.JmlToTextual;
import de.uka.ilkd.key.speclang.translation.SLExpression;

import org.key_project.util.collection.ImmutableList;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import org.antlr.v4.runtime.ParserRuleContext;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Locks the translation of the locset names {@code \nothing}, {@code \strictly_nothing} and
 * {@code \everything} through the JMLtk front-end (JMLTK_GAPS S15). JMLtk has no grammar token
 * for these names and surfaces them as plain {@code NameExpr}s, but it keeps the leading
 * backslash in the name; {@code JmlToTextual} re-serializes them verbatim and KeY's own JML
 * grammar re-parses them into the special tokens that {@code Translator} maps to the special
 * frame terms ({@code TermBuilder.empty()}/{@code strictlyNothing()}/{@code createdLocs()}).
 * Each test asserts that the JMLtk round-trip produces exactly the same term as the legacy
 * (pre-takeover) clause text.
 */
public class LocsetClauseTranslationTest {
    private Services services;
    private Translator translator;

    @BeforeEach
    public void setup() {
        if (services != null) {
            return;
        }
        services = TacletForTests.services();
        JavaService r2k = services.getJavaService();
        r2k.parseSpecialClasses();
        var kjt = new KeYJavaType(JavaDLTheory.ANY);
        var tRef = new TypeRef(kjt);
        LocationVariable self = new LocationVariable(new ProgramElementName("self"), tRef);
        LocationVariable result = new LocationVariable(new ProgramElementName("result"), tRef);
        LocationVariable exc = new LocationVariable(new ProgramElementName("exc"), tRef);
        translator = new Translator(services, kjt, self, SpecMathMode.defaultMode(),
            ImmutableList.nil(), result, exc, new HashMap<>(), new HashMap<>());
    }

    /**
     * Parses a single JML clause with KeY's own grammar (the pre-takeover path) and returns the
     * term the Translator produces for it.
     */
    private JTerm legacyTerm(String clauseText) {
        var ctx = JmlFacade.parseClause(clauseText);
        var sl = (SLExpression) ctx.accept(translator);
        return sl.getTerm();
    }

    /**
     * Runs the JMLtk front-end on a method carrying the given JML comment and returns the term
     * the Translator produces for the resulting (re-parsed) clause.
     */
    private JTerm jmltkTerm(String jmlComment) {
        var sl = (SLExpression) reParsedClause(jmlComment).accept(translator);
        return sl.getTerm();
    }

    @Test
    public void strictlyNothingAssignClauseKeepsItsMeaning() {
        JTerm legacy = legacyTerm("assignable \\strictly_nothing;");
        JTerm jmltk = jmltkTerm("//@ assignable \\strictly_nothing;");
        assertEquals(legacy, jmltk);
    }

    @Test
    public void nothingAssignClauseKeepsItsMeaning() {
        JTerm legacy = legacyTerm("assignable \\nothing;");
        JTerm jmltk = jmltkTerm("//@ assignable \\nothing;");
        assertEquals(legacy, jmltk);
    }

    @Test
    public void everythingAssignClauseKeepsItsMeaning() {
        JTerm legacy = legacyTerm("assignable \\everything;");
        JTerm jmltk = jmltkTerm("//@ assignable \\everything;");
        assertEquals(legacy, jmltk);
    }

    @Test
    public void modifiesNothingClauseKeepsItsMeaning() {
        JTerm legacy = legacyTerm("assignable \\nothing;");
        JTerm jmltk = jmltkTerm("//@ modifies \\nothing;");
        assertEquals(legacy, jmltk);
    }

    @Test
    public void theJmltkRoundsTripReParsesTheSpecialTokens() {
        // the re-serialized clause must pick the special terminals, not a store-ref name
        var strictlyNothing = reParsedClause("//@ assignable \\strictly_nothing;");
        assertInstanceOf(JmlParser.Assignable_clauseContext.class, strictlyNothing);
        assertNotNull(storerefOf(strictlyNothing).STRICTLY_NOTHING());
        var nothing = reParsedClause("//@ assignable \\nothing;");
        assertNotNull(storerefOf(nothing).NOTHING());
        var everything = reParsedClause("//@ assignable \\everything;");
        assertNotNull(storerefOf(everything).EVERYTHING());
    }

    /**
     * The single storeref of the re-parsed assignable clause (the special locset names re-parse
     * through the storeRefUnion alternative, not the dedicated assignable-clause terminal).
     */
    private static JmlParser.StorerefContext storerefOf(ParserRuleContext clause) {
        return ((JmlParser.Assignable_clauseContext) clause).storeRefUnion().storeRefList()
                .storeref(0);
    }

    private ParserRuleContext reParsedClause(String jmlComment) {
        String src = "class C {\n" + jmlComment + "\npublic void m() {\n}\n}\n";
        ParserConfiguration config = new ParserConfiguration();
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.RAW);
        config.setProcessJml(true);
        config.setKeepJmlDocs(true);
        config.setJmlKeys(List.of(List.of("key")));
        var result = new JavaParser(config).parse(src);
        if (!result.isSuccessful()) {
            throw new AssertionError("JMLtk parse failed: " + result.getProblems());
        }
        CompilationUnit cu = result.getResult().get();
        ClassOrInterfaceDeclaration cls = cu.getTypes().get(0).asClassOrInterfaceDeclaration();
        MethodDeclaration m = cls.getMethods().get(0);
        JmlContract contract = m.getContracts().get(0);
        TextualJMLSpecCase specCase = JmlToTextual.toSpecCases(contract).get(0);
        ParserRuleContext clause = null;
        for (var c : specCase.getClauses()) {
            clause = c;
        }
        return clause;
    }
}
