/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.sourceview;

import java.awt.*;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;

import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.nparser.KeYLexer;

import org.antlr.v4.runtime.CharStreams;

import static de.uka.ilkd.key.nparser.KeYLexer.*;

/**
 * This is a lexer class used by a {@link SourceHighlightDocument} to highlight KeY code.
 * It uses the ANTLR lexer {@link KeYLexer} to tokenize the text.
 *
 * Secondary keywords are highlighted in a different color. These are schema variables kinds,
 * variable conditions etc.
 *
 * @author Mattias Ulbrich
 */
public class KeYEditorLexer implements SourceHighlightDocument.EditorLexer {

    /** highight color for KeY keywords (dark red/violet) */
    private static final ColorSettings.ColorProperty KEYWORD_COLOR =
        ColorSettings.define("[key]keyword", "", new Color(0x7f0055));

    /** highight color for secondary KeY keywords (light red/violet) */
    private static final ColorSettings.ColorProperty KEYWORD2_COLOR =
        ColorSettings.define("[key]keyword2", "", new Color(0x78526C));

    /** highight color for comments (dull green) */
    private static final ColorSettings.ColorProperty COMMENT_COLOR =
        ColorSettings.define("[key]comment", "", new Color(0x3f7f5f));

    /** highight color for literals (dark blue) */
    private static final ColorSettings.ColorProperty LITERAL_COLOR =
        ColorSettings.define("[key]literal", "", new Color(0x2A75B1));

    /** highight color for Modalities (dark yellow) */
    private static final ColorSettings.ColorProperty MODALITY_COLOR =
        ColorSettings.define("[key]modality", "", new Color(0xC67C13));

    /** default style */
    private static final SimpleAttributeSet normalStyle = new SimpleAttributeSet();

    /** the style of keywords */
    private static final SimpleAttributeSet commentStyle = new SimpleAttributeSet();

    /** the style of keywords */
    private static final SimpleAttributeSet keywordStyle = new SimpleAttributeSet();

    /** the style of secondary keywords */
    private static final SimpleAttributeSet keyword2Style = new SimpleAttributeSet();

    /** the style of literals */
    private static final SimpleAttributeSet literalStyle = new SimpleAttributeSet();

    /** the style of comments and line comments */
    private static final SimpleAttributeSet modalityStyle = new SimpleAttributeSet();

    /** the token identifiers for keywords */
    private static final BitSet KEYWORDS = new BitSet();

    /** the token identifiers for secondary keywords */
    private static final BitSet KEYWORDS2 = new BitSet();

    /** the token identifiers for literals */
    private static final BitSet LITERALS = new BitSet();

    /** the token identifiers for comments */
    private static final BitSet COMMENTS = new BitSet();

    /** the token identifiers for modalities */
    private static final BitSet MODALITIES = new BitSet();

    static {
        // set the styles
        // StyleConstants.setBold(keywordStyle, true);
        StyleConstants.setForeground(keywordStyle, KEYWORD_COLOR.get());
        StyleConstants.setForeground(keyword2Style, KEYWORD2_COLOR.get());
        StyleConstants.setForeground(commentStyle, COMMENT_COLOR.get());
        StyleConstants.setForeground(literalStyle, LITERAL_COLOR.get());
        StyleConstants.setForeground(modalityStyle, MODALITY_COLOR.get());

        // the following can probably be refined
        addAll(KEYWORDS, SORTS, GENERIC, PROXY, EXTENDS, ONEOF, ABSTRACT, SCHEMAVARIABLES,
            SCHEMAVAR, MODIFIABLE, PROGRAMVARIABLES, STORE_TERM_IN, STORE_STMT_IN, HAS_INVARIANT,
            GET_INVARIANT, GET_FREE_INVARIANT, GET_VARIANT, IS_LABELED, SAME_OBSERVER, VARCOND,
            FORALL, EXISTS, SUBST, IF, IFEX, THEN, ELSE, INCLUDE, INCLUDELDTS, CLASSPATH,
            BOOTCLASSPATH, NODEFAULTCLASSES, JAVASOURCE, WITHOPTIONS, OPTIONSDECL, KEYSETTINGS,
            PROFILE, SAMEUPDATELEVEL, INSEQUENTSTATE, ANTECEDENTPOLARITY, SUCCEDENTPOLARITY,
            CLOSEGOAL, HEURISTICSDECL, NONINTERACTIVE, DISPLAYNAME, HELPTEXT, REPLACEWITH, ADDRULES,
            ADDPROGVARS, HEURISTICS, FIND, ADD, ASSUMES, TRIGGER, AVOID, PREDICATES, FUNCTIONS,
            DATATYPES, TRANSFORMERS, UNIQUE, FREE, RULES, AXIOMS, PROBLEM, CHOOSECONTRACT,
            PROOFOBLIGATION, PROOF, PROOFSCRIPT, CONTRACTS, INVARIANTS, LEMMA, IN_TYPE,
            IS_ABSTRACT_OR_INTERFACE, CONTAINERTYPE);
        addAll(KEYWORDS2, MODALOPERATOR, PROGRAM, FORMULA, TERM, UPDATE, VARIABLES, VARIABLE,
            SKOLEMTERM, SKOLEMFORMULA, TERMLABEL, VARIABLES, VARIABLE, APPLY_UPDATE_ON_RIGID,
            DEPENDINGON, DISJOINTMODULONULL, DROP_EFFECTLESS_ELEMENTARIES, DROP_EFFECTLESS_STORES,
            SIMPLIFY_IF_THEN_ELSE_UPDATE, ENUM_CONST, FREELABELIN, HASSORT, FIELDTYPE, FINAL,
            ELEMSORT, HASLABEL, HASSUBFORMULAS, ISARRAY, ISARRAYLENGTH, ISCONSTANT, ISENUMTYPE,
            ISINDUCTVAR, ISLOCALVARIABLE, ISOBSERVER, DIFFERENT, METADISJOINT, ISTHISREFERENCE,
            DIFFERENTFIELDS, ISREFERENCE, ISREFERENCEARRAY, ISSTATICFIELD, ISMODELFIELD,
            ISINSTRICTFP, ISSUBTYPE, EQUAL_UNIQUE, NEW, NEW_TYPE_OF, NEW_DEPENDING_ON,
            NEW_LOCAL_VARS, HAS_ELEMENTARY_SORT, NEWLABEL, CONTAINS_ASSIGNMENT, NOT_, NOTFREEIN,
            SAME, STATIC, STATICMETHODREFERENCE, MAXEXPANDMETHOD, STRICT, TYPEOF,
            INSTANTIATE_GENERIC);
        addAll(LITERALS, STRING_LITERAL, HEX_LITERAL, INT_LITERAL, FLOAT_LITERAL, DOUBLE_LITERAL,
            REAL_LITERAL, TRUE, FALSE);
        addAll(COMMENTS, DOC_COMMENT, ML_COMMENT, SL_COMMENT);
        addAll(MODALITIES, MODALITY);
    }

    private static void addAll(BitSet bitSet, int... values) {
        for (int value : values) {
            bitSet.set(value);
        }
    }

    private SimpleAttributeSet getAttributes(int type) {
        if (KEYWORDS.get(type)) {
            return keywordStyle;
        } else if (KEYWORDS2.get(type)) {
            return keyword2Style;
        } else if (LITERALS.get(type)) {
            return literalStyle;
        } else if (COMMENTS.get(type)) {
            return commentStyle;
        } else if (MODALITIES.get(type)) {
            return modalityStyle;
        } else {
            return normalStyle;
        }
    }

    @Override
    public List<SourceHighlightDocument.Token> applyTo(String text) {
        KeYLexer keYLexer = new KeYLexer(CharStreams.fromString(text));
        List<SourceHighlightDocument.Token> result = new ArrayList<>();
        var t = keYLexer.nextToken();
        while (t.getType() != -1) {
            result.add(new SourceHighlightDocument.Token(t.getText().length(),
                getAttributes(t.getType())));
            t = keYLexer.nextToken();
        }
        return result;
    }
}
