/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Base abstract class for all AST nodes providing common position tracking.
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public abstract class BaseAstNode implements AstNode {
    protected final Position position;
    protected @Nullable AstNode parent;

    protected BaseAstNode(Position position) {
        this.position = position;
    }

    @Override
    public @Nullable AstNode getParent() {
        return parent;
    }

    public void setParent(@Nullable AstNode parent) {
        this.parent = parent;
    }

    @Override
    public Position getPosition() {
        return position;
    }

    protected void setChildParent(@Nullable AstNode child) {
        if (child instanceof BaseAstNode) {
            ((BaseAstNode) child).setParent(this);
        }
    }
}