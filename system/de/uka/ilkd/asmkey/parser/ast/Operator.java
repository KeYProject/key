// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.ast;


/** Operator symbols. There is only a private constructor. The
 * instances of this class are compared by reference.
 *
 * @author Hubert Schmid
 */

public final class Operator {

    /** big and */
    public static final Operator BIGAND = new Operator("And");

    /** big or */
    public static final Operator BIGOR = new Operator("Or");

    /** Logical equivalence. */
    public static final Operator EQV = new Operator("<->");

    /** Logical implication. */
    public static final Operator IMP = new Operator("->");

    /** Logical or. */
    public static final Operator OR = new Operator("|");

    /** Logical and. */
    public static final Operator AND = new Operator("&");

    /** Logical not. */
    public static final Operator NOT = new Operator("!");

    /** Equivalence on universe. */
    public static final Operator EQUALS = new Operator("=");

    /** Logical true. */
    public static final Operator TRUE = new Operator("TRUE");

    /** Logical false. */
    public static final Operator FALSE = new Operator("FALSE");

    /** Integer addition. */
    public static final Operator ADD = new Operator("+");

    /** Integer substraction. */
    public static final Operator SUB = new Operator("-");

    /** Integer multiplication. */
    public static final Operator MULT = new Operator("*");

    /** Integer division. */
    public static final Operator DIV = new Operator("/");

    /** Negation (unary minus). */
    public static final Operator NEG = new Operator("-");

    /** Timed operation  */
    public static final Operator STEP = new Operator("_");

    public static final Operator TERM_EQUALS = new Operator("==");
    public static final Operator TERM_AND = new Operator("and");
    public static final Operator TERM_ANDALSO = new Operator("and also");
    public static final Operator TERM_OR = new Operator("or");
    public static final Operator TERM_ORELSE = new Operator("or else");
    public static final Operator TERM_IF = new Operator("if");

    /** A textual representation of this operator. This may be used
     * only for debugging. */
    private final String text;


    /** only predefined instances. */
    private Operator(String text) {
        this.text = text;
    }


    /** for debug only */
    public String toString() {
        return "[Operator:" + text + "]";
    }

}
