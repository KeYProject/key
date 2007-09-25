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


/** AstQuantifier represents a quantifier (all and exists) in the
 * input stream. It consists of a quantifier symbol and the location
 * in the input.
 *
 * @see Quantifier
 * @author Hubert Schmid
 */

public final class AstQuantifier extends AstNode {

    /** The actual quantifier symbol. */
    private final Quantifier q;


    public AstQuantifier(Location location, Quantifier q) {
        super(location);
        this.q = q;
    }

    /** Returns the actual quantifier symbol. */
    public Quantifier getQuantifier() {
        return q;
    }

}
