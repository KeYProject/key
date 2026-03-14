/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.util.List;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.label.OriginTermLabelFactory;
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
    public static final Path testFile = HelperClassForTests.TESTCASE_DIRECTORY
            .resolve("speclang")
            .resolve("testFile.key");

    private final PreParser preParser;

    public NJmlTranslatorTests() {
        JavaInfo javaInfo =
            HelperClassForTests.parse(testFile).getFirstProof().getJavaInfo();
        Services services = javaInfo.getServices();
        services.setOriginFactory(new OriginTermLabelFactory());
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

    @Test
    void testWarnRequires() throws URISyntaxException {
        preParser.clearWarnings();
        String contract = "/*@ requires true; ensures true; requires true;";
        ImmutableList<TextualJMLConstruct> result =
            preParser.parseClassLevel(contract, new URI("Test.java"), Position.newOneBased(5, 5));
        assertNotNull(result);
        List<PositionedString> warnings = preParser.getWarnings();
        PositionedString message = warnings.getFirst();
        assertEquals(
            "Diverging Semantics from JML Reference: Requires does not initiate a new contract. "
                + "See https://keyproject.github.io/key-docs/user/JMLGrammar/#TODO ("
                + Path.of("Test.java").toUri() + ", 1/34)",
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
            jml.getModifiers());
    }

    @Test
    void testContractModifiersMultiple() {
        preParser.clearWarnings();
        String contracts = """
                /*@ public abstract final normal_behaviour
                  @ requires true;
                  @ private static exceptional_behaviour
                  @ requires false;
                  @*/""";
        ImmutableList<TextualJMLConstruct> result =
            preParser.parseClassLevel(contracts, null, Position.newOneBased(5, 5));
        assertNotNull(result);
        assertEquals(2, result.size());
        TextualJMLConstruct jml = result.head();
        assertEquals(ImmutableList.of(JMLModifier.PUBLIC, JMLModifier.ABSTRACT, JMLModifier.FINAL),
            jml.getModifiers());
        jml = result.tail().head();
        assertEquals(ImmutableList.of(JMLModifier.PRIVATE, JMLModifier.STATIC),
            jml.getModifiers());
    }

    @Test
    void testContractModifiersMultipleAlso() {
        preParser.clearWarnings();
        String contracts = """
                /*@ public abstract final normal_behaviour
                  @ requires true;
                  @ also\s
                  @ private static exceptional_behaviour
                  @ requires false;
                  @*/""";
        ImmutableList<TextualJMLConstruct> result =
            preParser.parseClassLevel(contracts, null, Position.newOneBased(5, 5));
        assertNotNull(result);
        assertEquals(2, result.size());
        TextualJMLConstruct jml = result.head();
        assertEquals(ImmutableList.of(JMLModifier.PUBLIC, JMLModifier.ABSTRACT, JMLModifier.FINAL),
            jml.getModifiers());
        jml = result.tail().head();
        assertEquals(ImmutableList.of(JMLModifier.PRIVATE, JMLModifier.STATIC),
            jml.getModifiers());
    }
}
