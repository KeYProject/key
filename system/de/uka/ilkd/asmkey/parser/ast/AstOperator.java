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


import de.uka.ilkd.key.parser.Location;


/** AstOperator represents an operator (like implication, conjunction,
 * etc) in the input stream. It consists of an operator symbol and the
 * location in the input.
 *
 * @see Operator
 * @author Hubert Schmid
 */

public final class AstOperator extends AstNode {

    /** The actual operator symbol. */
    private final Operator op;


    public AstOperator(Location location, Operator op) {
        super(location);
        this.op = op;
    }


    /** Returns the actual operator symbol. */
    public Operator getOperator() {
        return op;
    }

}
