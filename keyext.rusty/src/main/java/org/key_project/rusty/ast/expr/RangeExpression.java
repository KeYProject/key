/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public record RangeExpression(@Nullable Expr left,@Nullable Expr right,boolean inclusive)implements Expr{@Override public void visit(Visitor v){v.performActionOnRangeExpression(this);}

@Override public @NonNull SyntaxElement getChild(int n){if(n==0&&left!=null)return left;if(left!=null)--n;if(n==0&&right!=null)return right;throw new IndexOutOfBoundsException("RangeExpression has less than "+n+" children");}

@Override public int getChildCount(){int c=0;if(left!=null)++c;if(right!=null)++c;return c;}

@Override public String toString(){StringBuilder sb=new StringBuilder();if(left!=null)sb.append(left);sb.append("..");if(inclusive)sb.append('=');if(right!=null)sb.append(right);return sb.toString();}

    @Override
    public Type type(Services services) {
        throw new UnsupportedOperationException();
    }}
