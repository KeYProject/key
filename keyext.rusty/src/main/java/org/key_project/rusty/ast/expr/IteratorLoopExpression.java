/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.Label;
import org.key_project.rusty.ast.abstraction.TupleType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.pat.Pattern;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public record IteratorLoopExpression(@Nullable Label label,Pattern pattern,Expr expr,BlockExpression body)implements LoopExpression{@Override public void visit(Visitor v){v.performActionOnIteratorLoopExpression(this);}

@Override public @NonNull SyntaxElement getChild(int n){if(n==0&&label!=null){return label;}if(label!=null){--n;}if(n==0)return pattern;if(n==1)return expr;if(n==2)return body;throw new IndexOutOfBoundsException();}

@Override public int getChildCount(){int c=0;if(label!=null){++c;}return c+3;}

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (label != null) sb.append(label).append(": ");
        sb.append("for ").append(pattern).append(" in ").append(body);
        return sb.toString();
    }

    @Override
    public Type type(Services services) {
        return TupleType.UNIT;
    }
}
