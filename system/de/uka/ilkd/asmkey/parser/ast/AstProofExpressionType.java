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


/** Instances of this class represents proof expression types
 * (ids). There is only a private constructor. Instances of this class
 * are compared by reference.
 *
 * @author Hubert Schmid
 */

public final class AstProofExpressionType {

    public static final AstProofExpressionType FORMULA = new AstProofExpressionType("formula");

    public static final AstProofExpressionType TERM = new AstProofExpressionType("term");

    public static final AstProofExpressionType RULE = new AstProofExpressionType("rule");

    public static final AstProofExpressionType BUILTIN = new AstProofExpressionType("builtin");

    public static final AstProofExpressionType BRANCH = new AstProofExpressionType("branch");

    public static final AstProofExpressionType INST = new AstProofExpressionType("inst");

    public static final AstProofExpressionType IFSEQFORMULA = new AstProofExpressionType("ifseqformula");

    public static final AstProofExpressionType INTERACTIVE = new AstProofExpressionType("interactive");

    public static final AstProofExpressionType HEURISTICS = new AstProofExpressionType("heur");


    /* Logging */
    public static final AstProofExpressionType LOG = new AstProofExpressionType("log");
    
    public static final AstProofExpressionType USER = new AstProofExpressionType("user");

    public static final AstProofExpressionType VERSION = new AstProofExpressionType("keyVersion");

    /* Dieser Fall wird beim Laden des Beweises fuer irgendwas
     * benoetigt. Allerdings wird der Identifier selbst nicht
     * verwendet. */
    public static final AstProofExpressionType IDENT = new AstProofExpressionType("ident");


    /** A textual representation of this expression type. This may be
     * used only for debugging. */
    private final String text;


    /** only predefined instances */
    AstProofExpressionType(String text) {
        this.text = text;
    }


    /** for debug only */
    public String toString() {
        return "[ProofExpressionType:" + text + "]";
    }

}
