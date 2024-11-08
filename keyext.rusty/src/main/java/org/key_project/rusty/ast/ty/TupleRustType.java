/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.ty;

import java.util.stream.Collectors;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.abstraction.TupleType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.collection.ImmutableArray;

public class TupleRustType implements RustType {
    private final ImmutableArray<RustType> types;
    private final Type type;

    public static TupleRustType UNIT = new TupleRustType(new ImmutableArray<>());

    public TupleRustType(ImmutableArray<RustType> types) {
        this.types = types;
        this.type =
            TupleType.getInstance(types.stream().map(RustType::type).collect(Collectors.toList()));
    }

    @Override
    public Type type() {
        return type;
    }

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
