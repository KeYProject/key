/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration.modifier;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.declaration.Modifier;

/**
 * Transient.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Transient extends Modifier {

    /**
     * Transient.
     */

    public Transient() {}

    /**
     * Transient.
     *
     * @param children
     *        the children of this AST element as KeY classes. May contain: Comments
     */

    public Transient(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }

    /**
     * Get symbol.
     *
     * @return the string.
     */

    protected String getSymbol() {
        return "transient";
    }
}
