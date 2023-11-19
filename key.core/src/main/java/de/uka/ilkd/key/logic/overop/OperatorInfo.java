/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.overop;

import de.uka.ilkd.key.nparser.KeYLexer;

import org.key_project.util.collection.ImmutableArray;

import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.pp.NotationInfo.*;


/**
 * Information Table about all operators in KeY.
 */
public enum OperatorInfo {
    /**
     * // (8918) ⋖ LESS-THAN WITH DOT kleiner als mit Punkt
     */
    LESS_THAN_WITH_DOT(KeYLexer.LESS_THAN_WITH_DOT, PRIORITY_COMPARISON, '⋖'),
    /**
     * (8922) ⋚ LESS-THAN EQUAL TO OR GREATER-THAN kleiner als, gleich oder größer als
     */
    LESS_THAN_EQUAL_TO_OR_GREATER_THAN(KeYLexer.LESS_THAN_EQUAL_TO_OR_GREATER_THAN,
            PRIORITY_COMPARISON, '⋚'),
    /**
     * (8920) ⋘ VERY MUCH LESS-THAN Sehr viel kleiner als
     */
    VERY_MUCH_LESS_THAN(KeYLexer.VERY_MUCH_LESS_THAN, PRIORITY_COMPARISON, '⋘'),
    /**
     * (8924) ⋜ EQUAL TO OR LESS-THAN gleich oder kleiner als
     */
    EQUAL_TO_OR_LESS_THAN(KeYLexer.EQUAL_TO_OR_LESS_THAN, PRIORITY_COMPARISON, '⋜'),
    /**
     * (8926) ⋞ EQUAL TO OR PRECEDES gleich oder vorangehend
     */
    EQUAL_TO_OR_PRECEDES(KeYLexer.EQUAL_TO_OR_PRECEDES, PRIORITY_COMPARISON, '⋞'),
    /**
     * (8828) ≼ PRECEDES OR EQUAL TO vorangehend oder gleich
     */
    PRECEDES_OR_EQUAL_TO(KeYLexer.PRECEDES_OR_EQUAL_TO, PRIORITY_COMPARISON, '≼'),
    /**
     * (8928) ⋠ DOES NOT PRECEDE OR EQUAL weder vorangehend oder gleich
     */
    DOES_NOT_PRECEDE_OR_EQUAL("⋠", KeYLexer.DOES_NOT_PRECEDE_OR_EQUAL, PRIORITY_COMPARISON,
            OperatorInfo.PRECEDES_OR_EQUAL_TO),
    /**
     * (8849) ⊑ SQUARE IMAGE OF OR EQUAL TO viereckiges Bild oder gleich
     */
    SQUARE_IMAGE_OF_OR_EQUAL_TO(KeYLexer.SQUARE_IMAGE_OF_OR_EQUAL_TO, PRIORITY_COMPARISON, '⊑'),

    /**
     * (8930) ⋢ NOT SQUARE IMAGE OF OR EQUAL TO kein viereckiges Bild oder gleich
     */
    NOT_SQUARE_IMAGE_OF_OR_EQUAL_TO("⋢", KeYLexer.NOT_SQUARE_IMAGE_OF_OR_EQUAL_TO,
            PRIORITY_COMPARISON,
            SQUARE_IMAGE_OF_OR_EQUAL_TO),
    /**
     * (8932) ⋤ SQUARE IMAGE OF OR NOT EQUAL TO viereckiges Bild oder ungleich
     */
    SQUARE_IMAGE_OF_OR_NOT_EQUAL_TO(KeYLexer.SQUARE_IMAGE_OF_OR_NOT_EQUAL_TO, PRIORITY_COMPARISON,
            '⋤'),
    /**
     * (8826) ≺ PRECEDES vorangehend
     */
    PRECEDES(KeYLexer.PRECEDES, PRIORITY_COMPARISON, '≺'),
    /**
     * (8830) ≾ PRECEDES OR EQUIVALENT TO vorangehend oder äquivalent
     */
    PRECEDES_OR_EQUIVALENT_TO(KeYLexer.PRECEDES_OR_EQUIVALENT_TO, PRIORITY_COMPARISON, '≾'),
    /**
     * (8836) ⊄ NOT A SUBSET OF ist keine ;// (echte) Teilmenge von
     */
    NOT_A_SUBSET_OF(KeYLexer.NOT_A_SUBSET_OF, PRIORITY_COMPARISON, '⊄'),
    /**
     * (8838) ⊆ SUBSET OF OR EQUAL TO Teilmenge oder gleich
     */
    SUBSET_OF_OR_EQUAL_TO(KeYLexer.SUBSET_OF_OR_EQUAL_TO, PRIORITY_COMPARISON, '⊆', "\\subseteq"),

    /**
     * ∖ SET MINUS
     */
    SET_MINUS(KeYLexer.SETMINUS, PRIORITY_ARITH_WEAK, '∖', "\\setminus"),

    // (8848) ⊐ SQUARE ORIGINAL OF viereckiges Original
    SQUARE_ORIGINAL_OF(KeYLexer.SQUARE_ORIGINAL, PRIORITY_COMPARISON, '⊐'),
    // (8850) ⊒ SQUARE ORIGINAL OF OR EQUAL TO viereckiges Original oder gleich
    SQUARE_ORIGINAL_OF_OR_EQUAL_TO(KeYLexer.SQUARE_ORIGINAL_OF_OR_EQUAL_TO, PRIORITY_COMPARISON,
            '⊒'),
    // (8919) ⋗ GREATER-THAN WITH DOT größer als mit Punkt
    GREATER_THAN_WITH_DOT(KeYLexer.GREATER_THAN_WITH_DOT, PRIORITY_COMPARISON, '⋗', "\\gedot"),
    // (8921) ⋙ VERY MUCH GREATER-THAN sehr viel größer als
    VERY_MUCH_GREATER_THAN(KeYLexer.VERY_MUCH_GREATER_THAN, PRIORITY_COMPARISON, '⋙', "\\gg"),
    // (8923) ⋛ GREATER-THAN EQUAL TO OR LESS-THAN größer als, gleich oder kleiner als
    GREATER_THAN_EQUAL_TO_OR_LESS_THAN(KeYLexer.GREATER_THAN_EQUAL_TO_OR_LESS_THAN,
            PRIORITY_COMPARISON, '⋛'),
    // (8925) ⋝ EQUAL TO OR GREATER-THAN gleich oder größer als
    EQUAL_TO_OR_GREATER_THAN(KeYLexer.EQUAL_TO_OR_GREATER_THAN, PRIORITY_COMPARISON, '⋝'),
    // (8927) ⋟ EQUAL TO OR SUCCEEDS gleich oder nachfolgend
    EQUAL_TO_OR_SUCCEEDS(KeYLexer.EQUAL_TO_OR_SUCCEEDS, PRIORITY_COMPARISON, '⋟'),
    // (8929) ⋡ DOES NOT SUCCEED OR EQUAL weder nachfolgend oder gleich
    DOES_NOT_SUCCEED_OR_EQUAL(KeYLexer.DOES_NOT_SUCCEED_OR_EQUAL, PRIORITY_COMPARISON, '⋡'),
    // (8931) ⋣ NOT SQUARE ORIGINAL OF OR EQUAL TO kein viereckiges Original oder gleich
    NOT_SQUARE_ORIGINAL_OF_OR_EQUAL_TO(KeYLexer.NOT_SQUARE_ORIGINAL_OF_OR_EQUAL_TO,
            PRIORITY_COMPARISON, '⋣'),
    // (8933) ⋥ SQUARE ORIGINAL OF OR NOT EQUAL TO viereckiges Original oder ungleich
    SQUARE_ORIGINAL_OF_OR_NOT_EQUAL_TO(KeYLexer.SQUARE_ORIGINAL_OF_OR_NOT_EQUAL_TO,
            PRIORITY_COMPARISON, '⋥'),
    // (8827) ≻ SUCCEEDS nachfolgend
    SUCCEEDS(KeYLexer.SUCCEEDS, PRIORITY_COMPARISON, '≻'),
    // (8829) ≽ SUCCEEDS OR EQUAL TO nachfolgend oder gleich
    SUCCEEDS_OR_EQUAL_TO(KeYLexer.SUCCEEDS_OR_EQUAL_TO, PRIORITY_COMPARISON, '≽'),
    // (8831) ≿ SUCCEEDS OR EQUIVALENT TO nachfolgend oder äquivalent
    SUCCEEDS_OR_EQUIVALENT_TO(KeYLexer.SUCCEEDS_OR_EQUIVALENT_TO, PRIORITY_COMPARISON, '≿'),
    // (8832) ⊀ DOES NOT PRECEDE nicht vorangehend
    DOES_NOT_PRECEDE(KeYLexer.DOES_NOT_PRECEDE, PRIORITY_COMPARISON, '⊀'),
    // (8833) ⊁ DOES NOT SUCCEED nicht nachfolgend
    DOES_NOT_SUCCEED(KeYLexer.DOES_NOT_SUCCEED, PRIORITY_COMPARISON, '⊁'),
    // (8835) ⊃ SUPERSET OF ist ;// (echte) Obermenge von
    SUPERSET_OF(KeYLexer.SUPERSET_OF, PRIORITY_COMPARISON, '⊃'),
    // (8837) ⊅ NOT A SUPERSET OF ist keine ;// (echte) Obermenge von
    NOT_A_SUPERSET_OF(KeYLexer.NOT_A_SUPERSET_OF, PRIORITY_COMPARISON, '⊅'),

    // (8839) ⊇ SUPERSET OF OR EQUAL TO Obermenge oder gleich
    SUPERSET_OF_OR_EQUAL_TO(KeYLexer.SUPERSET_OF_OR_EQUAL_TO, PRIORITY_COMPARISON, '⊇'),

    // (8847) ⊏ SQUARE IMAGE OF viereckiges Bild
    SQUARE_IMAGE_OF(KeYLexer.SQUARE_IMAGE_OF, PRIORITY_COMPARISON, '⊏'),


    GREATER(KeYLexer.GREATER, PRIORITY_COMPARISON, '>'),
    GREATER_EQUAL(KeYLexer.GREATEREQUAL, PRIORITY_COMPARISON, '≥', ">="),

    EQUALITY(KeYLexer.EQUALS, PRIORITY_COMPARISON, '↔', "<->"),

    LESS(KeYLexer.LESS, PRIORITY_COMPARISON, '<'),
    LESS_EQUAL(KeYLexer.LESSEQUAL, PRIORITY_COMPARISON, '≤', "<="),

    // (8853) ⊕ CIRCLED PLUS eingekreistes Pluszeichen
    CIRCLED_PLUS(KeYLexer.CIRCLED_PLUS, PRIORITY_ARITH_WEAK, '⊕'),

    // (8854) ⊖ CIRCLED MINUS eingekreistes Minuszeichen
    CIRCLED_MINUS(KeYLexer.CIRCLED_MINUS, PRIORITY_ARITH_WEAK, '⊖'),

    // (8862) ⊞ SQUARED PLUS eingerahmtes Pluszeichen
    SQUARED_PLUS(KeYLexer.SQUARED_PLUS, PRIORITY_ARITH_WEAK, '⊞'),

    // (8861) ⊝ CIRCLED DASH eingekreister Gedankenstrich
    CIRCLED_DASH(KeYLexer.CIRCLED_DASH, PRIORITY_ARITH_WEAK, '⊝'),

    // (8863) ⊟ SQUARED MINUS eingerahmtes Minuszeichen
    SQUARED_MINUS(KeYLexer.SQUARED_MINUS, PRIORITY_ARITH_WEAK, '⊟'),


    // STAR
    // (8855) ⊗ CIRCLED TIMES eingekreistes Multiplikationszeichen
    CIRCLED_TIMES(KeYLexer.CIRCLED_TIMES, PRIORITY_ARITH_STRONG, '⊗'),

    // (8857) ⊙ CIRCLED DOT OPERATOR eingekreister Punktoperator
    CIRCLED_DOT_OPERATOR(KeYLexer.CIRCLED_DOT_OPERATOR, PRIORITY_ARITH_STRONG, '⊙'),

    // (8859) ⊛ CIRCLED ASTERISK OPERATOR eingekreister Sternoperator
    CIRCLED_ASTERISK_OPERATOR(KeYLexer.CIRCLED_ASTERISK_OPERATOR, PRIORITY_ARITH_STRONG, '⊛'),

    // (8864) ⊠ SQUARED TIMES eingerahmtes Multiplikationszeichen
    SQUARED_TIMES(KeYLexer.SQUARED_TIMES, PRIORITY_ARITH_STRONG, '⊠'),

    // (8865) ⊡ SQUARED DOT OPERATOR eingerahmter Punktoperator
    SQUARED_DOT_OPERATOR(KeYLexer.SQUARED_DOT_OPERATOR, PRIORITY_ARITH_STRONG, '⊡'),

    // SLASH
    // (8858) ⊚ CIRCLED RING OPERATOR eingekreister Ringoperator
    CIRCLED_RING_OPERATOR(KeYLexer.CIRCLED_RING_OPERATOR, PRIORITY_ARITH_STRONG, '⊚'),

    // (8856) ⊘ CIRCLED DIVISION SLASH eingekreister Divisionsstrich
    CIRCLED_DIVISION_SLASH(KeYLexer.CIRCLED_DIVISION_SLASH, PRIORITY_ARITH_STRONG, '⊘'),


    EQUALS(KeYLexer.EQUALS, PRIORITY_EQUAL, '=', "="),

    NOT_EQUALS("≠", KeYLexer.NOT_EQUALS, "!=", KeYLexer.NOT_EQUALS, PRIORITY_EQUAL, null),

    // (8774) ≆ APPROXIMATELY BUT NOT ACTUALLY EQUAL TO ungefähr, aber nicht genau gleich
    APPROXIMATELY_BUT_NOT_ACTUALLY_EQUAL_TO(KeYLexer.APPROXIMATELY_BUT_NOT_ACTUALLY_EQUAL_TO,
            PRIORITY_EQUAL, '≆'),
    // (8775) ≇ NEITHER APPROXIMATELY NOR ACTUALLY EQUAL TO weder ungefähr noch genau gleich
    NEITHER_APPROXIMATELY_NOR_ACTUALLY_EQUAL_TO(
            KeYLexer.NEITHER_APPROXIMATELY_NOR_ACTUALLY_EQUAL_TO, PRIORITY_EQUAL, '≇'),
    // (8801) ≡ IDENTICAL TO ist kongruent zu
    IDENTICAL_TO(KeYLexer.IDENTICAL_TO, PRIORITY_EQUAL, '≡'),
    // (8802) ≢ NOT IDENTICAL TO ist nicht kongruent zu
    NOT_IDENTICAL_TO("≢", KeYLexer.NOT_IDENTICAL_TO, PRIORITY_EQUAL, IDENTICAL_TO),
    IMPLICATION(KeYLexer.IMP, PRIORITY_IMP, '→', "->"),
    OR(KeYLexer.OR, PRIORITY_OR, '∨'),
    // (8852) ⊔ SQUARE CUP nach oben geöffnetes Viereck
    SQUARE_CUP(KeYLexer.SQUARE_CUP, PRIORITY_OR, '⊔', "\\sqcup"),

    AND(KeYLexer.AND, PRIORITY_AND, '∧', "&"),

    // (8851) ⊓ SQUARE CAP nach unten geöffnetes Viereck
    SQUARE_CAP(KeYLexer.SQUARE_CAP, PRIORITY_AND, '⊓', "\\sqcap"),

    NEGATION(KeYLexer.NOT, PRIORITY_NEGATION, '¬', "!"),

    // (8860) ⊜ CIRCLED EQUALS eingekreistes Gleichheitszeichen
    CIRCLED_EQUALS(KeYLexer.CIRCLED_EQUALS, PRIORITY_EQUAL, '⊜'),

    UNION(KeYLexer.UNION, PRIORITY_OR, '∪', "\\cup"),
    INTERSECT(KeYLexer.INTERSECT, PRIORITY_AND, '∩', "\\cap"),
    ;


    private final int precedence;
    private final OperatorInfo positiveOperator;
    private final int tokenTypeAlt;
    private final int tokenTypeUtf8;
    private final String utf8;
    private final String alternative;

    OperatorInfo(int tokenType, int precedence, char operator) {
        this(String.valueOf(operator), tokenType, null, -1, precedence, null);
    }

    OperatorInfo(int tokenType, int precedence, char utf8, String longForm, int tokenTypeAlt) {
        this(String.valueOf(utf8), tokenType, longForm, tokenTypeAlt, precedence, null);
    }

    OperatorInfo(String utf8, int tokenTypeUtf8, @Nullable String alt, int tokenTypeAlt,
            int precedence,
            OperatorInfo positiveOperator) {
        this.tokenTypeUtf8 = tokenTypeUtf8;
        this.precedence = precedence;
        this.positiveOperator = positiveOperator;
        this.tokenTypeAlt = tokenTypeAlt;
        this.utf8 = utf8;
        this.alternative = alt;
    }

    OperatorInfo(String utf8, int tokenType, int precedence, OperatorInfo positiveOperator) {
        this(utf8, tokenType, null, -1, precedence, positiveOperator);
    }

    OperatorInfo(int tokenType, int precedence, char utf8, String longForm) {
        this(String.valueOf(utf8), tokenType, longForm, tokenType, precedence, null);
    }


    @Nullable
    public static OperatorInfo find(Token opToken) {
        for (OperatorInfo value : values()) {
            if (value.tokenTypeUtf8 == opToken.getType()
                    || value.tokenTypeAlt == opToken.getType()) {
                return value;
            }
        }
        return null;
    }

    public int getPrecedence() {
        return precedence;
    }


    public OperatorInfo getPositiveForm() {
        return positiveOperator;
    }

    public ImmutableArray<String> getNames() {
        if (alternative == null) {
            return new ImmutableArray<>(utf8);
        }
        return new ImmutableArray<>(utf8, alternative);
    }
}
