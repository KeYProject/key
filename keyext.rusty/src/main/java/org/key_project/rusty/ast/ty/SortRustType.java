/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.ty;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.abstraction.KeYRustyType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;

/**
 * Used for {@link KeYRustyType}s where there is no Rust type.
 */
public record SortRustType(KeYRustyType krt) implements RustType {
    @Override
    public Type type() { return krt; }

    @Override
    public void visit(Visitor v) { v.performActionOnSortRustType(this); }

    @Override
    public SyntaxElement getChild(int n) { throw new IndexOutOfBoundsException(); }

    @Override
    public int getChildCount() { return 0; }

    @Override
    public String toString() { return krt.getSort().toString(); }
}
