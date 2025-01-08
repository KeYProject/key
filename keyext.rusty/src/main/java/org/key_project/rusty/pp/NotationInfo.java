/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.pp;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.logic.op.Operator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.*;
import org.key_project.rusty.logic.op.sv.ModalOperatorSV;

public class NotationInfo {
    // Priorities of operators (roughly corresponding to the grammatical structure in the parser.
    static final int PRIORITY_TOP = 0;
    static final int PRIORITY_EQUIVALENCE = 20;
    static final int PRIORITY_IMP = 30;
    static final int PRIORITY_OR = 40;
    static final int PRIORITY_AND = 50;
    static final int PRIORITY_NEGATION = 60;
    static final int PRIORITY_QUANTIFIER = 60;
    static final int PRIORITY_MODALITY = 60;
    static final int PRIORITY_POST_MODALITY = 60;
    static final int PRIORITY_EQUAL = 70;
    static final int PRIORITY_COMPARISON = 80;
    static final int PRIORITY_ARITH_WEAK = 90;
    static final int PRIORITY_BELOW_ARITH_WEAK = 91;
    static final int PRIORITY_ARITH_STRONG = 100;
    static final int PRIORITY_BELOW_ARITH_STRONG = 101;
    static final int PRIORITY_CAST = 120;
    static final int PRIORITY_ATOM = 130;
    static final int PRIORITY_BOTTOM = 140;
    static final int PRIORITY_LABEL = 140; // TODO: find appropriate value

    public static boolean DEFAULT_PRETTY_SYNTAX = true;
    /**
     * Whether the very fancy notation is enabled in which Unicode characters for logical operators
     * are printed.
     */
    public static boolean DEFAULT_UNICODE_ENABLED = false;

    /**
     * This maps operators and classes of operators to {@link Notation}s. The idea is that we first
     * look whether the operator has a Notation registered. Otherwise, we see if there is one for
     * the <em>class</em> of the operator.
     */
    private HashMap<Object, Notation> notationTable;


    /**
     * Maps terms to abbreviations and reverse.
     */
    private AbbrevMap scm = new AbbrevMap();

    private boolean prettySyntax = DEFAULT_PRETTY_SYNTAX;

    private boolean unicodeEnabled = DEFAULT_UNICODE_ENABLED;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public NotationInfo() {
        this.notationTable = createDefaultNotation();
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    /**
     * Register the standard set of notations (that can be defined without a services object).
     */
    private HashMap<Object, Notation> createDefaultNotation() {

        HashMap<Object, Notation> tbl = new LinkedHashMap<>(50);

        tbl.put(Junctor.TRUE, new Notation.Constant("true", PRIORITY_ATOM));
        tbl.put(Junctor.FALSE, new Notation.Constant("false", PRIORITY_ATOM));
        tbl.put(Junctor.NOT, new Notation.Prefix("!", PRIORITY_NEGATION, PRIORITY_NEGATION));
        tbl.put(Junctor.AND,
            new Notation.Infix("&", PRIORITY_AND, PRIORITY_AND, PRIORITY_MODALITY));
        tbl.put(Junctor.OR, new Notation.Infix("|", PRIORITY_OR, PRIORITY_OR, PRIORITY_AND));
        tbl.put(Junctor.IMP, new Notation.Infix("->", PRIORITY_IMP, PRIORITY_OR, PRIORITY_IMP));
        tbl.put(Equality.EQV,
            new Notation.Infix("<->", PRIORITY_EQUIVALENCE, PRIORITY_EQUIVALENCE, PRIORITY_IMP));
        tbl.put(Quantifier.ALL,
            new Notation.Quantifier("\\forall", PRIORITY_QUANTIFIER, PRIORITY_QUANTIFIER));
        tbl.put(Quantifier.EX,
            new Notation.Quantifier("\\exists", PRIORITY_QUANTIFIER, PRIORITY_QUANTIFIER));
        tbl.put(Modality.RustyModalityKind.DIA,
            new Notation.ModalityNotation("\\<", "\\>", PRIORITY_MODALITY, PRIORITY_POST_MODALITY));
        tbl.put(Modality.RustyModalityKind.BOX,
            new Notation.ModalityNotation("\\[", "\\]", PRIORITY_MODALITY, PRIORITY_POST_MODALITY));
        tbl.put(ModalOperatorSV.class,
            new Notation.ModalSVNotation(PRIORITY_MODALITY, PRIORITY_POST_MODALITY));
        tbl.put(IfThenElse.IF_THEN_ELSE, new Notation.IfThenElse(PRIORITY_ATOM, "\\if"));
        // tbl.put(IfExThenElse.IF_EX_THEN_ELSE, new Notation.IfThenElse(PRIORITY_ATOM, "\\ifEx"));
        tbl.put(SubstOp.SUBST, new Notation.Subst());
        tbl.put(UpdateApplication.UPDATE_APPLICATION, new Notation.UpdateApplicationNotation());
        tbl.put(UpdateJunctor.PARALLEL_UPDATE, new Notation.ParallelUpdateNotation());

        tbl.put(RFunction.class, new Notation.FunctionNotation());
        tbl.put(LogicVariable.class, new Notation.VariableNotation());
        tbl.put(ProgramVariable.class, new Notation.VariableNotation());
        tbl.put(Equality.class,
            new Notation.Infix("=", PRIORITY_EQUAL, PRIORITY_COMPARISON, PRIORITY_COMPARISON));
        tbl.put(ElementaryUpdate.class, new Notation.ElementaryUpdateNotation());
        tbl.put(SchemaVariable.class, new Notation.SchemaVariableNotation());

        return tbl;
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    public void refresh(Services services) {
        refresh(services, DEFAULT_PRETTY_SYNTAX, DEFAULT_UNICODE_ENABLED);
    }

    public void refresh(Services services, boolean usePrettyPrinting, boolean useUnicodeSymbols) {
        this.unicodeEnabled = useUnicodeSymbols;
        this.prettySyntax = usePrettyPrinting;
        /*
         * if (usePrettyPrinting && services != null) {
         * if (useUnicodeSymbols) {
         * this.notationTable = createUnicodeNotation(services);
         * } else {
         * this.notationTable = createPrettyNotation(services);
         * }
         * } else
         */ {
            this.notationTable = createDefaultNotation();
        }
    }

    public AbbrevMap getAbbrevMap() {
        return scm;
    }


    public void setAbbrevMap(AbbrevMap am) {
        scm = am;
    }

    Notation getNotation(Class<?> c) {
        return notationTable.get(c);
    }

    /**
     * Get the Notation for a given Operator. If no notation is registered, a Function notation is
     * returned.
     */
    Notation getNotation(Operator op) {
        Notation result = notationTable.get(op);
        if (result != null) {
            return result;
        }

        result = notationTable.get(op.getClass());
        if (result != null) {
            return result;
        }

        if (op instanceof Modality mod) {
            result = notationTable.get(mod.kind());
            if (result != null) {
                return result;
            } else {
                result = notationTable.get(ModalOperatorSV.class);
                if (result != null) {
                    return result;
                }
            }
        }

        if (op instanceof SchemaVariable) {
            result = notationTable.get(SchemaVariable.class);
            if (result != null) {
                return result;
            }
        }

        return new Notation.FunctionNotation();
    }

    public boolean isPrettySyntax() {
        return prettySyntax;
    }

    public boolean isUnicodeEnabled() {
        return unicodeEnabled;
    }

    public Map<Object, Notation> getNotationTable() {
        return notationTable;
    }
}
