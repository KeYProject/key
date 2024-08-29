/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.Label;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public record BreakExpression(@Nullable Label label,@Nullable Expr expr)implements Expr{@Override public void visit(Visitor v){v.performActionOnBreakExpression(this);}

@Override public @NonNull SyntaxElement getChild(int n){if(n==0&&label!=null){return label;}if(label!=null){--n;}if(n==0&&expr!=null){return expr;}throw new IndexOutOfBoundsException("BreakExpression has only "+getChildCount()+" children");}

@Override public int getChildCount(){int c=0;if(label!=null){++c;}if(expr!=null){++c;}return c;}

@Override public String toString(){StringBuilder sb=new StringBuilder();sb.append("break");if(label!=null){sb.append(" ").append(label);}if(expr!=null){sb.append(" ").append(expr);}sb.append(";");return sb.toString();}}
