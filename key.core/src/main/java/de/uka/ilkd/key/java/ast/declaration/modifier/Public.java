/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration.modifier;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;


/**
 * Public.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Public extends VisibilityModifier {


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     */
    public Public() {
        super();
    }

    public Public(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }

    /**
     * Get symbol.
     *
     * @return the string.
     */
    protected String getSymbol() {
        return "public";
    }

    @Override
    public int compareTo(VisibilityModifier arg0) {
        if (arg0 instanceof Private) {
            return -3;
        }
        if (arg0 == null) {
            return -2;
        }
        if (arg0 instanceof Protected) {
            return -1;
        }
        if (arg0 instanceof Public) {
            return 0;
        }
        assert false;
        return 0;
    }
}
