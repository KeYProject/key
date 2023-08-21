/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.io.File;
import java.net.URI;
import java.net.URISyntaxException;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.JMLModifier;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (6/1/21)
 */
public class NJmlTranslatorTests {
    public static final String testFile = HelperClassForTests.TESTCASE_DIRECTORY + File.separator
        + "speclang" + File.separator + "testFile.key";
    private final PreParser preParser;

    public NJmlTranslatorTests() {
        JavaInfo javaInfo =
            new HelperClassForTests().parse(new File(testFile)).getFirstProof().getJavaInfo();
        Services services = javaInfo.getServices();
        KeYJavaType testClassType = javaInfo.getKeYJavaType("testPackage.TestClass");
        preParser = new PreParser();
    }

    @Test
    public void testIgnoreOpenJML() {
        preParser.clearWarnings();
        String contract = "/*+KEY@ invariant x == 4; */ /*+OPENJML@ invariant x == 54; */";
        ImmutableList<TextualJMLConstruct> result =
            preParser.parseClassLevel(contract, null, Position.newOneBased(1, 1));
        assertNotNull(result);
        assertEquals(1, result.size(), "Too many invariants found.");
    }

    // weigl: ignored since fix #1640, due to interface change
    // @Test
    // public void testModelMethodWithAtSignInBody() {
    // ImmutableList<TextualJMLConstruct> result =
    // jmlIO.parseClassLevel("/*@ model int f(int x) { \n" +
    // "@ return x+1; " +
    // "@ }*/", "Test.java", Position.newOneBased(0, 0));
    // assertNotNull(result);
    // TextualJMLMethodDecl decl = (TextualJMLMethodDecl) result.head();
    // assertEquals("int f (int x);", decl.getParsableDeclaration().trim());
    // String eqString = Translator.getEqualityExpressionOfModelMethod(decl.getDecl());
    // assertEquals("f(x) == (x+1)", eqString);
    // }
    //
    // @Test
    // public void testModelMethodWithAtSignInBody2() {
    // ImmutableList<TextualJMLConstruct> result =
    // jmlIO.parseClassLevel("/*@ model int f(int[] arr) { \n" +
    // "@ //this is a comment \n" +
    // "@ return arr[1]; //comment\n" +
    // "@ }*/", "Test.java", Position.newOneBased(0, 0));
    // assertNotNull(result);
    // TextualJMLMethodDecl decl = (TextualJMLMethodDecl) result.head();
    // assertEquals("int f (int[] arr);", decl.getParsableDeclaration().trim());
    // String eqString = Translator.getEqualityExpressionOfModelMethod(decl.getDecl());
    // assertEquals("f(arr) == (arr[1])", eqString);
    // }

    @Test
    public void testWarnRequires() throws URISyntaxException {
        preParser.clearWarnings();
        String contract = "/*@ requires true; ensures true; requires true;";
        ImmutableList<TextualJMLConstruct> result =
            preParser.parseClassLevel(contract, new URI("Test.java"), Position.newOneBased(5, 5));
        assertNotNull(result);
        ImmutableList<PositionedString> warnings = preParser.getWarnings();
        PositionedString message = warnings.head();
        assertEquals(
            "Diverging Semantics form JML Reference: Requires does not initiate a new contract. "
                + "See https://keyproject.github.io/key-docs/user/JMLGrammar/#TODO (Test.java, 5/38)",
            message.toString());
    }

    @Test
    void testContractModifiers() {
        preParser.clearWarnings();
        String contract = "/*@ public abstract final normal_behaviour\nrequires true;";
        ImmutableList<TextualJMLConstruct> result =
            preParser.parseClassLevel(contract, null, Position.newOneBased(5, 5));
        assertNotNull(result);
        assertEquals(1, result.size());
        TextualJMLConstruct jml = result.head();
        assertEquals(ImmutableList.of(JMLModifier.PUBLIC, JMLModifier.ABSTRACT, JMLModifier.FINAL),
            jml.getMods());
    }

    @Test
    void testContractModifiersMultiple() {
        preParser.clearWarnings();
        String contracts = "/*@ public abstract final normal_behaviour\n" +
            "  @ requires true;\n" +
            "  @ private static exceptional_behaviour\n" +
            "  @ requires false;\n" +
            "  @*/";
        ImmutableList<TextualJMLConstruct> result =
            preParser.parseClassLevel(contracts, null, Position.newOneBased(5, 5));
        assertNotNull(result);
        assertEquals(2, result.size());
        TextualJMLConstruct jml = result.head();
        assertEquals(ImmutableList.of(JMLModifier.PUBLIC, JMLModifier.ABSTRACT, JMLModifier.FINAL),
            jml.getMods());
        jml = result.tail().head();
        assertEquals(ImmutableList.of(JMLModifier.PRIVATE, JMLModifier.STATIC),
            jml.getMods());
    }

    @Test
    void testContractModifiersMultipleAlso() {
        preParser.clearWarnings();
        String contracts = "/*@ public abstract final normal_behaviour\n" +
            "  @ requires true;\n" +
            "  @ also \n" +
            "  @ private static exceptional_behaviour\n" +
            "  @ requires false;\n" +
            "  @*/";
        ImmutableList<TextualJMLConstruct> result =
            preParser.parseClassLevel(contracts, null, Position.newOneBased(5, 5));
        assertNotNull(result);
        assertEquals(2, result.size());
        TextualJMLConstruct jml = result.head();
        assertEquals(ImmutableList.of(JMLModifier.PUBLIC, JMLModifier.ABSTRACT, JMLModifier.FINAL),
            jml.getMods());
        jml = result.tail().head();
        assertEquals(ImmutableList.of(JMLModifier.PRIVATE, JMLModifier.STATIC),
            jml.getMods());
    }
}
