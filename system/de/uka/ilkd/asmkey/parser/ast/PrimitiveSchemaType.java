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


/** Instances of this class represents primitive schema types for
 * schema variables. There is only a private constructor. Instances of
 * this class are compared by reference.
 *
 * @author Hubert Schmid
 */

public final class PrimitiveSchemaType {

    /** Schema type for formulas. */
    public static final PrimitiveSchemaType FORMULA = new PrimitiveSchemaType("FORMULA");

    /** Schema type for arbitrary asm rules. */
    public static final PrimitiveSchemaType ASMRULE = new PrimitiveSchemaType("ASMRULE");


    /** A textual representation of this schema type. This may be used
     * only for debugging. */
    private final String text;


    /** only predefined instances */
    PrimitiveSchemaType(String text) {
        this.text = text;
    }


    /** for debug only */
    public String toString() {
        return "[PrimitiveSchemaType:" + text + "]";
    }

}
