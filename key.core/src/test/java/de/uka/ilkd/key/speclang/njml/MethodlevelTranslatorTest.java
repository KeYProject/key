/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.io.IOException;
import java.io.InputStream;
import java.util.List;
import java.util.stream.Stream;

import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLMethodDecl;

import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;

import static org.junit.jupiter.api.Assertions.*;

/**
 * @author Alexander Weigl
 * @version 1 (5/15/20)
 */
public class MethodlevelTranslatorTest {
    @TestFactory
    public Stream<DynamicTest> getFiles() throws IOException {
        InputStream resourceAsStream =
            ExpressionTranslatorTest.class.getResourceAsStream("methodlevel.txt");
        return ClasslevelTranslatorTest.readInputs(resourceAsStream, this::parseAndInterpret);
    }

    public void parseAndInterpret(String expr) {
        assertNotEquals("", expr);
        JmlLexer lexer = JmlFacade.createLexer(expr);
        JmlParser parser = new JmlParser(new CommonTokenStream(lexer));
        try {
            JmlParser.Methodlevel_commentContext ctx = parser.methodlevel_comment();
            if (parser.getNumberOfSyntaxErrors() != 0) {
                debugLexer(expr);
            }
        } catch (Exception e) {
            debugLexer(expr);
        }
        assertEquals(0, parser.getNumberOfSyntaxErrors());
    }

    @Test
    public void parseModelMethodsNullable() {
        String modelMethodNullable = """
                /*@ public model_behavior
                    requires true;
                    accessible n, this.a;
                    model nullable Object foo(nullable Nullable n) {
                                return null;
                    }
                @*/
                """;
        JmlLexer lexer = JmlFacade.createLexer(modelMethodNullable);
        JmlParser parser = new JmlParser(new CommonTokenStream(lexer));
        JmlParser.Classlevel_commentsContext ctx = null;
        try {
            ctx = parser.classlevel_comments();
            if (parser.getNumberOfSyntaxErrors() != 0) {
                debugLexer(modelMethodNullable);
            }
        } catch (Exception e) {
            debugLexer(modelMethodNullable);
            System.out.println(e.getMessage());
        }
        assertEquals(0, parser.getNumberOfSyntaxErrors());

        // Test parser
        List<JmlParser.ModifierContext> modelMethodModifiers =
            ctx.classlevel_comment(1).modifiers().modifier();
        assertTrue(modelMethodModifiers.stream().anyMatch(it -> it.NULLABLE() != null));
        JmlParser.Param_listContext modelMethodParameters =
            ctx.classlevel_comment(2).classlevel_element().method_declaration().param_list();
        assertTrue(
            modelMethodParameters.param_decl().stream().anyMatch(it -> it.NULLABLE() != null));

        // Test translation
        final TextualTranslator translator = new TextualTranslator(false);
        ctx.accept(translator);
        final var translationOpt =
            translator.constructs.stream().filter(c -> c instanceof TextualJMLMethodDecl)
                    .findFirst();

        assertTrue(translationOpt.isPresent(), "No model method declaration found");
        final var methodDecl =
            ((TextualJMLMethodDecl) translationOpt.get()).getParsableDeclaration();
        assertTrue(methodDecl.contains("/*@ nullable @*/ Object"), "Return value is not nullable");
        assertTrue(methodDecl.contains("/*@ nullable @*/ Nullable n"), "Parameter is not nullable");
    }

    @Test
    public void parseModelMethodsNonNull() {
        String modelMethodNullable = """
                /*@ public model_behavior
                    requires true;
                    accessible n, this.a;
                    model non_null Object foo(non_null Nullable n) {
                                return null;
                    }
                @*/
                """;
        JmlLexer lexer = JmlFacade.createLexer(modelMethodNullable);
        JmlParser parser = new JmlParser(new CommonTokenStream(lexer));
        JmlParser.Classlevel_commentsContext ctx = null;
        try {
            ctx = parser.classlevel_comments();
            if (parser.getNumberOfSyntaxErrors() != 0) {
                debugLexer(modelMethodNullable);
            }
        } catch (Exception e) {
            debugLexer(modelMethodNullable);
        }
        assertEquals(0, parser.getNumberOfSyntaxErrors());

        // Test parser

        List<JmlParser.ModifierContext> modelMethodModifiers =
            ctx.classlevel_comment(1).modifiers().modifier();
        assertTrue(modelMethodModifiers.stream().anyMatch(it -> it.NON_NULL() != null));
        JmlParser.Param_listContext modelMethodParameters =
            ctx.classlevel_comment(2).classlevel_element().method_declaration().param_list();
        assertTrue(
            modelMethodParameters.param_decl().stream().anyMatch(it -> it.NON_NULL() != null));

        // Test translation

        final TextualTranslator translator = new TextualTranslator(false);
        ctx.accept(translator);
        final var translationOpt =
            translator.constructs.stream().filter(c -> c instanceof TextualJMLMethodDecl)
                    .findFirst();

        assertTrue(translationOpt.isPresent(), "No model method declaration found");
        final var methodDecl =
            ((TextualJMLMethodDecl) translationOpt.get()).getParsableDeclaration();
        assertTrue(methodDecl.contains("/*@ non_null @*/ Object"), "Return value is not non_null");
        assertTrue(methodDecl.contains("/*@ non_null @*/ Nullable n"), "Parameter is not non_null");

    }

    private void debugLexer(String expr) {
        JmlLexer lexer = JmlFacade.createLexer(expr);
        DebugJmlLexer.debug(lexer);
    }
}
