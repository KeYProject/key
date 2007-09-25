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


/** Quantifier symbols. There is only a private constructor. The
 * instances of this class are compared by reference.
 *
 * @author Hubert Schmid
 */

public final class Quantifier {

    /** universal quantifier symbol. */
    public static final Quantifier ALL = new Quantifier("all");

    /** existencial quantifier symbol. */
    public static final Quantifier EX = new Quantifier("ex");


    /** A textual representation of this quantifier. This may be used
     * only for debugging. */
    private final String text;


    /** only predefined instances. */
    private Quantifier(String text) {
        this.text = text;
    }


    /** for debug only */
    public String toString() {
        return "[Quantifier:" + text + "]";
    }

}
