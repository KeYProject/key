/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

// spotless:off
public record Label(Name name) implements RustyProgramElement {
    @Override
    public @NonNull SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Label has no children");
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public void visit(Visitor v) {

    }
}
//spotless:on
