package org.key_project.key.ast;

import org.jspecify.annotations.Nullable;

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
     * Get the source code position range of this node.
     *
     * @return The position containing start and end line/column information
     */
    @Nullable Position getPosition();
}
