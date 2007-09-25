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


import de.uka.ilkd.asmkey.parser.tree.DeclarationParser;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;

/** AST node for declarations. All nodes for declarations
 * (e.g. variables, taclets, sorts) that needs only one pass (either late
 * or early) are instances of
 * subclasses of this class. Every declaration owns an identifier. See
 * {@link #accept} and {@link AstDeclarationVisitor} for more
 * information.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */


public abstract class AstSinglePassDeclaration extends AstDeclaration {

    public AstSinglePassDeclaration(Location location, Identifier id) {
	super(location, id);
    }

    /** This methods calls the corresponding method in visitor. for the first pass
     * @see DeclarationParser
     **/
    public abstract void accept(AstDeclarationVisitor visitor) throws ParserException;

    /** for debug only */
    public String toString() {
        return "[AstSinglePassDeclaration:id=" + getId() + toString2() + "]";
    }

    /** used by toString() (only for debug purpose) */
    protected abstract String toString2();

}
