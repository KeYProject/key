/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import java.awt.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.swing.*;
import javax.swing.text.*;

import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.nparser.ParsingFacade;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.nparser.KeYLexer.*;

/**
 * Utilities for highlighting of text based on ANTLR-based Lexers.
 *
 * @author Alexander Weigl
 * @version 1 (2/17/26)
 */
@NullMarked
public abstract class LexerHighlighter {
    protected abstract @Nullable AttributeSet getStyle(int tokenType);

    private final StyleContext styleContext = new StyleContext();

    protected AttributeSet define(Color fgColor, boolean bold, boolean italic) {
        AttributeSet aset =
            styleContext.addAttribute(SimpleAttributeSet.EMPTY, StyleConstants.Foreground, fgColor);
        aset = styleContext.addAttribute(aset, StyleConstants.FontFamily, Font.MONOSPACED);
        aset = styleContext.addAttribute(aset, StyleConstants.Bold, bold);
        aset = styleContext.addAttribute(aset, StyleConstants.Italic, italic);
        return aset;
    }

    public final void highlightPaneMarkdown(JTextPane contentPane) {
        String text = contentPane.getText();
        Pattern pattern = getMarkdownPattern();

        Matcher match = pattern.matcher(text);
        var sd = contentPane.getStyledDocument();

        while (match.find()) {
            var lexer = ParsingFacade.createLexer(CharStreams.fromString(match.group(1)));
            var toks = lexer.getAllTokens();
            int startIdx = match.start() + "```key".length();
            for (var tok : toks) {
                highlightToken(sd, startIdx, tok);
            }
        }
        contentPane.invalidate();
        contentPane.repaint();
        contentPane.repaint();
    }

    public final void highlightPaneAll(JTextPane contentPane, int startIdx, int stopIdx) {
        String text = contentPane.getText();

        if (stopIdx < 0) {
            stopIdx = text.length();
        }

        text = text.substring(startIdx, stopIdx);

        var sd = contentPane.getStyledDocument();
        var lexer = ParsingFacade.createLexer(CharStreams.fromString(text));
        var toks = lexer.getAllTokens();
        for (var tok : toks) {
            highlightToken(sd, startIdx, tok);
        }
        contentPane.invalidate();
        contentPane.repaint();
        contentPane.repaint();
    }

    public final void highlightPaneAll(JTextPane contentPane) {
        highlightPaneAll(contentPane, 0, -1);
    }


    private void highlightToken(StyledDocument sd, int startIdx, Token tok) {
        var attribute = getStyle(tok.getType());
        sd.setCharacterAttributes(startIdx + tok.getStartIndex(),
            1 + tok.getStopIndex() - tok.getStartIndex(),
            attribute, true);
    }

    protected abstract Pattern getMarkdownPattern();

    public static class KeYLexerHighlighter extends LexerHighlighter {
        public static final ColorSettings.ColorProperty COLOR_KEYWORD =
            ColorSettings.define("syntax.keyword", "", Color.BLUE, Color.ORANGE);

        public static final ColorSettings.ColorProperty COLOR_IDENTIFIER =
            ColorSettings.define("syntax.identifier", "", Color.BLACK, Color.WHITE);

        public static final ColorSettings.ColorProperty COLOR_COMMENT =
            ColorSettings.define("syntax.comment", "", Color.GREEN, Color.GREEN);

        public static final ColorSettings.ColorProperty COLOR_OPERATORS =
            ColorSettings.define("syntax.operators", "", Color.BLACK, Color.ORANGE);

        public static final ColorSettings.ColorProperty COLOR_ERROR =
            ColorSettings.define("syntax.error", "", Color.RED, Color.WHITE);

        public static final ColorSettings.ColorProperty COLOR_LITERALS =
            ColorSettings.define("syntax.literals", "", Color.GREEN, Color.GREEN);


        private final AttributeSet STYLE_OPERATORS = define(COLOR_OPERATORS.get(), false, false);
        private final AttributeSet STYLE_ERROR = define(COLOR_ERROR.get(), false, false);
        private final AttributeSet STYLE_LITERALS = define(COLOR_LITERALS.get(), false, true);
        private final AttributeSet STYLE_KEYWORDS = define(COLOR_KEYWORD.get(), true, false);
        private final AttributeSet STYLE_IDENTIFIER = define(COLOR_IDENTIFIER.get(), true, false);
        private final AttributeSet STYLE_COMMENT = define(COLOR_COMMENT.get(), false, true);
        private final AttributeSet STYLE_DEFAULT = define(COLOR_IDENTIFIER.get(), false, false);

        private final Pattern MARKDOWN = Pattern.compile("```key(.*?)```",
            Pattern.MULTILINE | Pattern.DOTALL | Pattern.CASE_INSENSITIVE);

        @Override
        protected @Nullable AttributeSet getStyle(int tokType) {
            return switch (tokType) {
                case TERMLABEL, MODIFIABLE, PROGRAMVARIABLES, STORE_TERM_IN, STORE_STMT_IN,
                        HAS_INVARIANT, GET_INVARIANT, GET_FREE_INVARIANT, GET_VARIANT,
                        IS_LABELED, SAME_OBSERVER, VARCOND, APPLY_UPDATE_ON_RIGID,
                        DEPENDINGON, DISJOINTMODULONULL, DROP_EFFECTLESS_ELEMENTARIES,
                        DROP_EFFECTLESS_STORES, SIMPLIFY_IF_THEN_ELSE_UPDATE, ENUM_CONST,
                        FREELABELIN, HASSORT, FIELDTYPE, FINAL, ELEMSORT, HASLABEL,
                        HASSUBFORMULAS, ISARRAY, ISARRAYLENGTH, ISCONSTANT, ISENUMTYPE,
                        ISINDUCTVAR, ISLOCALVARIABLE, ISOBSERVER, DIFFERENT, METADISJOINT,
                        ISTHISREFERENCE, DIFFERENTFIELDS, ISREFERENCE, ISREFERENCEARRAY,
                        ISSTATICFIELD, ISMODELFIELD, ISINSTRICTFP, ISSUBTYPE, EQUAL_UNIQUE,
                        NEW, NEW_TYPE_OF, NEW_DEPENDING_ON, NEW_LOCAL_VARS, HAS_ELEMENTARY_SORT,
                        NEWLABEL, CONTAINS_ASSIGNMENT, NOT_, NOTFREEIN, SAME, STATIC,
                        STATICMETHODREFERENCE, MAXEXPANDMETHOD, STRICT, TYPEOF, INSTANTIATE_GENERIC,
                        FORALL, EXISTS, SUBST, IF, IFEX, THEN, ELSE, INCLUDE,
                        INCLUDELDTS, CLASSPATH, BOOTCLASSPATH, NODEFAULTCLASSES, JAVASOURCE,
                        WITHOPTIONS, OPTIONSDECL, KEYSETTINGS, PROFILE,
                        SAMEUPDATELEVEL, INSEQUENTSTATE, ANTECEDENTPOLARITY, SUCCEDENTPOLARITY,
                        CLOSEGOAL, HEURISTICSDECL, NONINTERACTIVE, DISPLAYNAME,
                        HELPTEXT, REPLACEWITH, ADDRULES, ADDPROGVARS, HEURISTICS,
                        FIND, ADD, ASSUMES, TRIGGER, AVOID, PREDICATES,
                        FUNCTIONS, DATATYPES, TRANSFORMERS, UNIQUE, FREE,
                        RULES, AXIOMS, PROBLEM, CHOOSECONTRACT, PROOFOBLIGATION,
                        PROOF, PROOFSCRIPT, CONTRACTS, INVARIANTS, LEMMA,
                        IN_TYPE, IS_ABSTRACT_OR_INTERFACE, IS_FINAL, CONTAINERTYPE,
                        SCHEMAVAR, FORMULA,
                        COMMENT_END, DOC_COMMENT, ML_COMMENT, MODALITYD, MODALITYB,
                        MODALITYBB, MODAILITYGENERIC1, MODAILITYGENERIC2, MODAILITYGENERIC3,
                        MODAILITYGENERIC4, MODAILITYGENERIC5, MODAILITYGENERIC6, MODAILITYGENERIC7,
                        MODALITYD_END, MODALITYD_STRING, MODALITYD_CHAR, MODALITYG_END,
                        MODALITYB_END, MODALITYBB_END ->
                    STYLE_KEYWORDS;

                case AT, PARALLEL, OR, AND, NOT, IMP,
                        EQUALS, NOT_EQUALS, SEQARROW, EXP, TILDE, PERCENT,
                        STAR, MINUS, PLUS, GREATER, GREATEREQUAL,
                        LESS, LESSEQUAL, LGUILLEMETS, RGUILLEMETS, EQV,
                        UTF_PRECEDES, UTF_IN, UTF_EMPTY, UTF_UNION, UTF_INTERSECT,
                        UTF_SUBSET_EQ, UTF_SUBSEQ, UTF_SETMINUS, SEMI, SLASH,
                        COLON, DOUBLECOLON, ASSIGN, DOT, DOTRANGE, COMMA,
                        LPAREN, RPAREN, LBRACE, RBRACE, LBRACKET, RBRACKET,
                        EMPTYBRACKETS ->
                    STYLE_OPERATORS;
                case ERROR_UKNOWN_ESCAPE, ERROR_CHAR -> STYLE_ERROR;
                case IDENT -> STYLE_IDENTIFIER;
                case COMMENT, SL_COMMENT -> STYLE_COMMENT;
                case CHAR_LITERAL, QUOTED_STRING_LITERAL, TRUE, FALSE,
                        STRING_LITERAL, BIN_LITERAL, HEX_LITERAL, INT_LITERAL, FLOAT_LITERAL,
                        DOUBLE_LITERAL, REAL_LITERAL ->
                    STYLE_LITERALS;
                default -> STYLE_DEFAULT;
            };
        }

        @Override
        protected Pattern getMarkdownPattern() {
            return MARKDOWN;
        }
    }
}
