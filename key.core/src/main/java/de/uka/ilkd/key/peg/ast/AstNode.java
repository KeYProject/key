/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Base interface for all AST nodes in the KeY PEG parser.
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public interface AstNode {
    /**
     * Accept a visitor to process this AST node.
     *
     * @param <T>     The return type of the visitor
     * @param visitor The visitor to accept
     * @return The result of visiting this node
     */
    default <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * Get the parent node of this AST node.
     *
     * @return The parent node, or null if this is a root node
     */
    @Nullable AstNode getParent();

    /**
     * Get the source code position range of this node.
     *
     * @return The position containing start and end line/column information
     */
    Position getPosition();
}
