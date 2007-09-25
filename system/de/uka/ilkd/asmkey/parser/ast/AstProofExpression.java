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


import java.util.List;

import de.uka.ilkd.asmkey.util.ArrayUtil;
import de.uka.ilkd.asmkey.util.CollectionUtil;
import de.uka.ilkd.key.parser.Location;


/** This class represents a proof expression.
 *
 * @author Hubert Schmid
 */

public final class AstProofExpression extends AstNode {

    /** Type of this expression. */
    private final AstProofExpressionType type;

    /** Content of this expression. */
    private final String text;

    /** List of child nodes. */
    private final List children;


    public AstProofExpression(Location location, AstProofExpressionType type, String text, AstProofExpression[] children) {
        //assert ant != null && suc != null;
        super(location);
        this.type = type;
        this.text = text;
        this.children = ArrayUtil.toList(children);
    }


    /** Returns the type of this proof expression. */
    public AstProofExpressionType getType() {
        return type;
    }

    /** Returns the content of this proof expression. */
    public String getText() {
        return text;
    }

    /** Returns (an umodifiable) list of the children of this
     * expression. */
    public List getChildren() {
        return children;
    }

    /** for debug only */
    public String toString() {
        return "[AstProofExpression:type=" + type + ",text=" + text + ",children=" + CollectionUtil.toString(children) + "]";
    }

}
