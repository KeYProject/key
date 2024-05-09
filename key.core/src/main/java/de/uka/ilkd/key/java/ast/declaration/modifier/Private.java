/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration.modifier;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;


/**
 * Private.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Private extends VisibilityModifier {

    /**
     * Private.
     */

    public Private() {}

    /**
     * Private
     *
     * @param children
     *        list of children. May contain: Comments
     */
    public Private(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }


    /**
     * Get symbol.
     *
     * @return the string.
     */
    protected String getSymbol() {
        return "private";
    }

    @Override
    public int compareTo(VisibilityModifier arg0) {
        if (arg0 instanceof Private) { return 0; }
        if (arg0 == null) { return 1; }
        if (arg0 instanceof Protected) { return 2; }
        if (arg0 instanceof Public) { return 3; }
        assert false;
        return 0;
    }
}
