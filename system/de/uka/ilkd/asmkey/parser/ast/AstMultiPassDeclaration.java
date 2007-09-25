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
 * (e.g. functions, predicates, rules) that needs many passes are instances of
 * subclasses of this class. Every declaration owns an identifier. See
 * {@link #accept} and {@link AstDeclarationVisitor} for more
 * information.
 *
 * @author Stanislas Nanchen
 */


public abstract class AstMultiPassDeclaration extends AstDeclaration {

    
    public AstMultiPassDeclaration(Location location, Identifier id) {
        super(location, id);
    }
  
    /** This methods calls the corresponding method in visitor. for the first pass
     * @see DeclarationParser
     **/
    public abstract void acceptFirstPass(AstDeclarationVisitor visitor) throws ParserException;

    /** This methods calls the corresponding method in visitor. for the second pass
     * @see DeclarationParser
     **/
    public abstract void acceptSecondPass(AstDeclarationVisitor visitor) throws ParserException;

    /** This methods calls the corresponding method in visitor. for the third pass
     * @see DeclarationParser
     **/
    //public abstract void acceptThirdPass(AstDeclarationVisitor visitor) throws ParserException;

    /** This methods calls the corresponding method in visitor. for the fourth pass
     * @see DeclarationParser
     **/
    //public abstract void acceptFourthPass(AstDeclarationVisitor visitor) throws ParserException;

    /** for debug only */
    public String toString() {
        return "[AstMultiPassDeclaration:id=" + getId() + toString2() + "]";
    }

    /** used by toString() (only for debug purpose) */
    protected abstract String toString2();

}
