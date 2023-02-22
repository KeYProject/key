package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import org.antlr.v4.runtime.ParserRuleContext;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import javax.annotation.Nonnull;
import java.util.ArrayList;
import java.util.List;

public class PreParser {
    /** warnings */
    private ImmutableList<PositionedString> warnings = ImmutableSLList.nil();

    /** constructor */
    public PreParser() {}

    /**
     * Parses a JML constructs on class level, e.g., invariants and methods contracts, and returns a
     * parse tree.
     */
    public ImmutableList<TextualJMLConstruct> parseClassLevel(JmlLexer lexer) {
        @Nonnull
        JmlParser p = JmlFacade.createParser(lexer);
        JmlParser.Classlevel_commentsContext ctx = p.classlevel_comments();
        p.getErrorReporter().throwException();
        jmlCheck(ctx);
        TextualTranslator translator = new TextualTranslator();
        ctx.accept(translator);
        return translator.constructs;
    }

    private void jmlCheck(ParserRuleContext ctx) {
        List<PositionedString> warn = new ArrayList<>();
        for (JmlCheck check : JmlChecks.getJmlChecks()) {
            List<PositionedString> w = check.check(ctx);
            warn.addAll(w);
        }
        this.warnings = warnings.prepend(ImmutableList.fromList(warn));
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
        @Nonnull
        JmlParser p = JmlFacade.createParser(lexer);
        JmlParser.Methodlevel_commentContext ctx = p.methodlevel_comment();
        p.getErrorReporter().throwException();
        jmlCheck(ctx);
        TextualTranslator translator = new TextualTranslator();
        ctx.accept(translator);
        return translator.constructs;
    }

    /**
     * Parse and interpret class level comments.
     */
    public ImmutableList<TextualJMLConstruct> parseClassLevel(String concatenatedComment,
            String fileName, Position pos) {
        return parseClassLevel(new PositionedString(concatenatedComment, fileName, pos));
    }

    /**
     * Parse and interpret class level comments.
     */
    private ImmutableList<TextualJMLConstruct> parseClassLevel(PositionedString positionedString) {
        JmlLexer lexer = JmlFacade.createLexer(positionedString);
        return parseClassLevel(lexer);
    }

    /**
     * Parse and interpret the given string as a method level construct.
     */
    public ImmutableList<TextualJMLConstruct> parseMethodLevel(String concatenatedComment,
            String fileName, Position position) {
        return parseMethodLevel(new PositionedString(concatenatedComment, fileName, position));
    }

    /**
     * returns the gathered interpretation warnings, e.g., deprecated constructs.
     */
    public ImmutableList<PositionedString> getWarnings() {
        return warnings;
    }

    public void clearWarnings() {
        warnings = ImmutableSLList.nil();
    }
}
