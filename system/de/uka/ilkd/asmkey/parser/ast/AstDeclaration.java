// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.ast;


import de.uka.ilkd.key.parser.Location;

/** AST node for declarations. All nodes for declarations
 * (e.g. variables, taclets, sorts) are instances of
 * subclasses of this class. Every declaration owns an identifier. See
 * {@link #accept} and {@link AstDeclarationVisitor} for more
 * information.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */
public abstract class AstDeclaration extends AstNode {

    /** The name of this declaration (like variable/function name or
     * taclet name. */
    private final Identifier id;


    public AstDeclaration(Location location, Identifier id) {
        super(location);
        this.id = id;
    }


    /** Returns the name of this declaration. */
    public final Identifier getId() {
        return id;
    }

    public abstract String toString();

}
