/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
