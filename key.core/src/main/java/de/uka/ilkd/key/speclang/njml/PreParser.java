/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.net.URI;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.JMLModifier;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLModifierList;

import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.Nullable;

/**
 * Transforms pure text comments into {@link TextualJMLConstruct}s.
 */
public class PreParser {
    private final List<PositionedString> warnings = new ArrayList<>(8);

    /**
     * Parses a JML constructs on class level, e.g., invariants and methods contracts, and returns a
     * parse tree.
     */
    public ImmutableList<TextualJMLConstruct> parseClassLevel(JmlLexer lexer) {
        JmlParser p = JmlFacade.createParser(lexer);
        JmlParser.Classlevel_commentsContext ctx = p.classlevel_comments();
        p.getErrorReporter().throwException();
        jmlCheck(ctx);
        TextualTranslator translator = new TextualTranslator(
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());
        ctx.accept(translator);

        // Add a construct for dangling modifiers. The JMLTransformer should attach this to the
        // appropriate element
        if (!translator.mods.isEmpty()) {
            translator.constructs =
                translator.constructs.append(new TextualJMLModifierList(translator.mods));
        }

        return translator.constructs;
    }

    private void jmlCheck(ParserRuleContext ctx) {
        for (JmlCheck check : JmlChecks.getJmlChecks()) {
            List<PositionedString> w = check.check(ctx);
            this.warnings.addAll(w);
        }
    }


    /**
     * Parses a JML constructs on class level, e.g., invariants and methods contracts, and returns a
     * parse tree.
     */
    public ImmutableList<TextualJMLConstruct> parseClassLevel(String content) {
        return parseClassLevel(JmlFacade.createLexer(content));
    }

    /**
     * Parses a JML constructs which occurs inside methods (mostly JML statements) and returns a
     * parse tree.
     */
    public ImmutableList<TextualJMLConstruct> parseMethodLevel(PositionedString positionedString) {
        return parseMethodLevel(JmlFacade.createLexer(positionedString));
    }

    /**
     * Parses a JML constructs which occurs inside methods (mostly JML statements) and returns a
     * parse tree.
     */
    private ImmutableList<TextualJMLConstruct> parseMethodLevel(JmlLexer lexer) {
        JmlParser p = JmlFacade.createParser(lexer);
        JmlParser.Methodlevel_commentContext ctx = p.methodlevel_comment();
        p.getErrorReporter().throwException();
        jmlCheck(ctx);
        TextualTranslator translator = new TextualTranslator(
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());
        ctx.accept(translator);
        return translator.constructs;
    }

    /**
     * Parse and interpret a class level comment. Might "split" the comment (i.e., produce a list
     * of textual constructs), for instance if there is a method contract and a modifier inside the
     * given comment.
     */
    public ImmutableList<TextualJMLConstruct> parseClassLevel(String concatenatedComment,
            @Nullable URI fileName, Position pos) {
        return parseClassLevel(
            new PositionedString(concatenatedComment, new Location(fileName, pos)));
    }

    /**
     * Parse and interpret class level comments. Might "split" the comment (i.e., produce a list
     * of textual constructs), for instance if there is a method contract and a modifier inside the
     * given comment.
     */
    private ImmutableList<TextualJMLConstruct> parseClassLevel(PositionedString positionedString) {
        JmlLexer lexer = JmlFacade.createLexer(positionedString);
        return parseClassLevel(lexer);
    }

    /**
     * Parse and interpret the given string as a method level construct.
     */
    public ImmutableList<TextualJMLConstruct> parseMethodLevel(String concatenatedComment,
            @Nullable URI fileName, Position position) {
        return parseMethodLevel(
            new PositionedString(concatenatedComment, new Location(fileName, position)));
    }

    /**
     * returns the gathered interpretation warnings, e.g., deprecated constructs.
     */
    public List<PositionedString> getWarnings() {
        return warnings;
    }

    public void clearWarnings() {
        warnings.clear();
    }

    public ImmutableList<JMLModifier> parseModifiers(String modifiers) {
        JmlParser p = JmlFacade.createParser(JmlFacade.createLexer(modifiers));
        var ctx = p.modifiersEOF();
        p.getErrorReporter().throwException();
        TextualTranslator translator = new TextualTranslator(
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());
        ctx.accept(translator);
        return translator.mods;
    }
}
