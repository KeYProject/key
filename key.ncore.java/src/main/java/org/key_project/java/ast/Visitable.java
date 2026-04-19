package org.key_project.java.ast;

import org.key_project.java.ast.visitor.*;

/**
 *
 * @author Alexander Weigl
 * @version 1 (4/19/26)
 */
public interface Visitable {
    <R> R accept(Visitor<R> visitor);

    <R, A> R accept(ArgVisitor<R, A> visitor, A arg);

    void accept(VoidVisitor visitor);
}
