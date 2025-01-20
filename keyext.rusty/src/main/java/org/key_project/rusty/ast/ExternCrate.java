/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.Nullable;

/**
 * An {@code extern crate} item, with optional original crate name if the crate was renamed.
 * E.g., {@code extern crate foo} or {@code extern crate foo_bar as foo}.
 *
 * @param ident
 * @param origIdent
 */
// spotless:off
public record ExternCrate(String ident, @Nullable String origIdent) implements Item {
    @Override
    public void visit(Visitor v) {

    }

    @Override
    public SyntaxElement getChild(int n) {
        return null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }
}
//spotless:on
