/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import java.awt.*;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.swing.*;
import javax.swing.text.*;

import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.sourceview.SourceHighlightDocument;
import de.uka.ilkd.key.nparser.JavaKeYLexer;
import de.uka.ilkd.key.nparser.ParsingFacade;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.nparser.JavaKeYLexer.*;

/**
 * Utilities for highlighting of text based on ANTLR-based Lexers.
 *
 * @author Alexander Weigl
 * @version 1 (2/17/26)
 */
@NullMarked
public abstract class LexerHighlighter {
    private final StyleContext styleContext = new StyleContext();

    /// Get the style regarding the `tokenType` of the {@link Token}
    protected abstract @Nullable AttributeSet getStyle(int tokenType);

    /// Length of the Markdown language prefix in code blocks.
    protected abstract int getPatternPrefixLength();

    /// The regular expression to find code blocks
    protected abstract Pattern getMarkdownPattern();

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

        var prefixLength = getPatternPrefixLength();
        while (match.find()) {
            var lexer = ParsingFacade.createLexer(CharStreams.fromString(match.group(1)));
            var toks = lexer.getAllTokens();
            int startIdx = match.start() + prefixLength;
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
        if (attribute != null) {
            sd.setCharacterAttributes(startIdx + tok.getStartIndex(),
                1 + tok.getStopIndex() - tok.getStartIndex(),
                attribute, true);
        }
    }

    public SourceHighlightDocument.EditorLexer getEditorLexer() {
        return text -> {
            JavaKeYLexer keYLexer = new JavaKeYLexer(CharStreams.fromString(text));
            List<SourceHighlightDocument.Token> result = new ArrayList<>();
            var t = keYLexer.nextToken();
            while (t.getType() != -1) {
                result.add(new SourceHighlightDocument.Token(t.getText().length(),
                    getStyle(t.getType())));
                t = keYLexer.nextToken();
            }
            return result;
        };
    }

    public static class KeYLexerHighlighter extends LexerHighlighter {

        /**
         * highlight color for KeY keywords (dark red/violet)
         */
        private static final ColorSettings.ColorProperty COLOR_KEYWORD =
            ColorSettings.define("syntax.key.keyword", "highlight color for KeY keywords ",
                new Color(0x7f0055));

        /**
         * highlight color for secondary KeY keywords (light red/violet)
         */
        private static final ColorSettings.ColorProperty COLOR_KEYWORD2 =
            ColorSettings.define("syntax.key.keyword2",
                "highlight color for secondary KeY keywords", new Color(0x78526C));

        /**
         * highlight color for comments (dull green)
         */
        private static final ColorSettings.ColorProperty COLOR_COMMENT =
            ColorSettings.define("syntax.key.comment", "highlight color for comments",
                new Color(0xafafaf));

        private static final ColorSettings.ColorProperty COLOR_COMMENT_DOC =
            ColorSettings.define("syntax.key.comment", "highlight color for documentation comments",
                new Color(0x3f7f5f));

        /**
         * highlight color for literals (dark blue)
         */
        private static final ColorSettings.ColorProperty COLOR_LITERALS =
            ColorSettings.define("syntax.key.literal", "highlight color for literals",
                new Color(0x2A75B1));

        /**
         * highlight color for Modalities (dark yellow)
         */
        private static final ColorSettings.ColorProperty COLOR_MODALITY =
            ColorSettings.define("syntax.key.modality", "highlight color for Modalities",
                new Color(0xC67C13));

        public static final ColorSettings.ColorProperty COLOR_IDENTIFIER =
            ColorSettings.define("infotree.syntax.identifier", "", Color.BLACK, Color.WHITE);

        public static final ColorSettings.ColorProperty COLOR_OPERATORS =
            ColorSettings.define("infotree.syntax.operators", "", Color.BLACK, Color.ORANGE);

        public static final ColorSettings.ColorProperty COLOR_ERROR =
            ColorSettings.define("infotree.syntax.error", "", Color.RED, Color.WHITE);


        private final AttributeSet STYLE_OPERATORS = define(COLOR_OPERATORS.get(), false, false);
        private final AttributeSet STYLE_ERROR = define(COLOR_ERROR.get(), false, false);
        private final AttributeSet STYLE_LITERALS = define(COLOR_LITERALS.get(), false, true);
        private final AttributeSet STYLE_KEYWORDS = define(COLOR_KEYWORD.get(), true, false);
        private final AttributeSet STYLE_KEYWORDS2 = define(COLOR_KEYWORD2.get(), false, false);
        private final AttributeSet STYLE_IDENTIFIER = define(COLOR_IDENTIFIER.get(), true, false);
        private final AttributeSet STYLE_COMMENT = define(COLOR_COMMENT.get(), false, true);
        private final AttributeSet STYLE_COMMENT2 = define(COLOR_COMMENT_DOC.get(), false, true);
        private final AttributeSet STYLE_MODALITY = define(COLOR_MODALITY.get(), false, true);
        private final AttributeSet STYLE_DEFAULT = define(COLOR_IDENTIFIER.get(), false, false);

        private final BitSet KEYWORDS = new BitSet();
        private final BitSet KEYWORDS2 = new BitSet();
        private final BitSet LITERALS = new BitSet();
        private final BitSet COMMENTS = new BitSet();
        private final BitSet COMMENTS2 = new BitSet();
        private final BitSet MODALITIES = new BitSet();
        private final BitSet IDENTIFIERS = new BitSet();
        private final BitSet ERROR = new BitSet();
        private final BitSet OPERATORS = new BitSet();

        public KeYLexerHighlighter() {
            // the following can probably be refined
            addAll(KEYWORDS, SORTS, GENERIC, PROXY, EXTENDS, ONEOF, ABSTRACT, SCHEMAVARIABLES,
                SCHEMAVAR, MODIFIABLE, PROGRAMVARIABLES, STORE_TERM_IN, STORE_STMT_IN,
                HAS_INVARIANT,
                GET_INVARIANT, GET_FREE_INVARIANT, GET_VARIANT, IS_LABELED, SAME_OBSERVER, VARCOND,
                FORALL, EXISTS, SUBST, IF, IFEX, THEN, ELSE, INCLUDE, INCLUDELDTS, CLASSPATH,
                BOOTCLASSPATH, NODEFAULTCLASSES, JAVASOURCE, WITHOPTIONS, OPTIONSDECL, KEYSETTINGS,
                PROFILE, SAMEUPDATELEVEL, INSEQUENTSTATE, ANTECEDENTPOLARITY, SUCCEDENTPOLARITY,
                CLOSEGOAL, HEURISTICSDECL, NONINTERACTIVE, DISPLAYNAME, HELPTEXT, REPLACEWITH,
                ADDRULES,
                ADDPROGVARS, HEURISTICS, FIND, ADD, ASSUMES, TRIGGER, AVOID, PREDICATES, FUNCTIONS,
                DATATYPES, TRANSFORMERS, UNIQUE, FREE, RULES, AXIOMS, PROBLEM, CHOOSECONTRACT,
                PROOFOBLIGATION, PROOF, PROOFSCRIPT, CONTRACTS, INVARIANTS, LEMMA, IN_TYPE,
                IS_ABSTRACT_OR_INTERFACE, CONTAINERTYPE,
                TERMLABEL, MODIFIABLE, PROGRAMVARIABLES, STORE_TERM_IN, STORE_STMT_IN,
                HAS_INVARIANT, GET_FREE_INVARIANT, GET_VARIANT,
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
                SCHEMAVAR, FORMULA, MODALITYD, MODALITYB,
                MODALITYBB, MODAILITYGENERIC1, MODAILITYGENERIC2, MODAILITYGENERIC3,
                MODAILITYGENERIC4, MODAILITYGENERIC5, MODAILITYGENERIC6, MODAILITYGENERIC7,
                MODALITYD_END, MODALITYD_STRING, MODALITYD_CHAR, MODALITYG_END,
                MODALITYB_END, MODALITYBB_END, PROGRAM);
            addAll(KEYWORDS2, MODALOPERATOR, PROGRAM, FORMULA, TERM, UPDATE, VARIABLES, VARIABLE,
                SKOLEMTERM, SKOLEMFORMULA, TERMLABEL, VARIABLES, VARIABLE, APPLY_UPDATE_ON_RIGID,
                DEPENDINGON, DISJOINTMODULONULL, DROP_EFFECTLESS_ELEMENTARIES,
                DROP_EFFECTLESS_STORES,
                SIMPLIFY_IF_THEN_ELSE_UPDATE, ISENUMCONST, FREELABELIN, HASSORT, FIELDTYPE, FINAL,
                ELEMSORT, HASLABEL, HASSUBFORMULAS, ISARRAY, ISARRAYLENGTH, ISCONSTANT,
                ISINDUCTVAR, ISLOCALVARIABLE, ISOBSERVER, DIFFERENT, METADISJOINT, ISTHISREFERENCE,
                DIFFERENTFIELDS, ISREFERENCE, ISREFERENCEARRAY, ISSTATICFIELD, ISMODELFIELD,
                ISINSTRICTFP, ISSUBTYPE, EQUAL_UNIQUE, NEW, NEW_TYPE_OF, NEW_DEPENDING_ON,
                NEW_LOCAL_VARS, HAS_ELEMENTARY_SORT, NEWLABEL, CONTAINS_ASSIGNMENT, NOT_, NOTFREEIN,
                SAME, STATIC, STATICMETHODREFERENCE, MAXEXPANDMETHOD, STRICT, TYPEOF,
                INSTANTIATE_GENERIC);
            addAll(OPERATORS, AT, PARALLEL, OR, AND, NOT, IMP,
                EQUALS, NOT_EQUALS, SEQARROW, EXP, TILDE, PERCENT,
                STAR, MINUS, PLUS, GREATER, GREATEREQUAL,
                LESS, LESSEQUAL, LGUILLEMETS, RGUILLEMETS, EQV,
                UTF_PRECEDES, UTF_IN, UTF_EMPTY, UTF_UNION, UTF_INTERSECT,
                UTF_SUBSET_EQ, UTF_SUBSEQ, UTF_SETMINUS, SEMI, SLASH,
                COLON, DOUBLECOLON, ASSIGN, DOT, DOTRANGE, COMMA,
                LPAREN, RPAREN, LBRACE, RBRACE, LBRACKET, RBRACKET,
                EMPTYBRACKETS);
            addAll(ERROR, ERROR_UKNOWN_ESCAPE, ERROR_CHAR);
            addAll(IDENTIFIERS, IDENT);
            addAll(LITERALS,
                CHAR_LITERAL, QUOTED_STRING_LITERAL, TRUE, FALSE,
                STRING_LITERAL, BIN_LITERAL, HEX_LITERAL, INT_LITERAL, FLOAT_LITERAL,
                DOUBLE_LITERAL, REAL_LITERAL);
            addAll(COMMENTS2, DOC_COMMENT);
            addAll(COMMENTS, ML_COMMENT, SL_COMMENT, COMMENT_END);
            addAll(MODALITIES, MODALITY);
        }

        private static void addAll(BitSet bitSet, int... values) {
            for (int value : values) {
                bitSet.set(value);
            }
        }


        @Override
        protected @Nullable AttributeSet getStyle(int type) {
            if (KEYWORDS.get(type)) {
                return STYLE_KEYWORDS;
            } else if (KEYWORDS2.get(type)) {
                return STYLE_KEYWORDS2;
            } else if (LITERALS.get(type)) {
                return STYLE_LITERALS;
            } else if (COMMENTS2.get(type)) {
                return STYLE_COMMENT2;
            } else if (COMMENTS.get(type)) {
                return STYLE_COMMENT;
            } else if (ERROR.get(type)) {
                return STYLE_ERROR;
            } else if (IDENTIFIERS.get(type)) {
                return STYLE_IDENTIFIER;
            } else if (OPERATORS.get(type)) {
                return STYLE_OPERATORS;
            } else if (MODALITIES.get(type)) {
                return STYLE_MODALITY;
            } else {
                return STYLE_DEFAULT;
            }
        }

        @Override
        protected int getPatternPrefixLength() {
            return "```key".length();
        }

        @Override
        protected Pattern getMarkdownPattern() {
            return Pattern.compile("```key(.*?)```",
                Pattern.MULTILINE | Pattern.DOTALL | Pattern.CASE_INSENSITIVE);
        }
    }
}
