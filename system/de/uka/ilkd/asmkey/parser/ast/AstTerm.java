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


import de.uka.ilkd.asmkey.parser.tree.ParsingStack;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;


/** AST node for terms. All AST nodes for terms are instances of this
 * class. See {@link #accept} and {@link AstTermVisitor} for more
 * information.
 *
 * @author Hubert Schmid
 */

public abstract class AstTerm extends AstNode {

    public AstTerm(Location location) {
        super(location);
    }


    /** This methods calls the corresponding method in visitor. The
     * object closure and the return value are passed through. */
    public abstract Object accept(AstTermVisitor visitor, ParsingStack closure) throws ParserException;

}
