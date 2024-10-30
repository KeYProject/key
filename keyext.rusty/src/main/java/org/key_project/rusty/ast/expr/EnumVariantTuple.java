/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.PathInExpression;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;

public record EnumVariantTuple(PathInExpression path,ImmutableArray<Expr>elements)implements EnumVariantExpression{@Override public void visit(Visitor v){v.performActionOnEnumVariantTuple(this);}

@Override public @NonNull SyntaxElement getChild(int n){if(n==0)return path;return Objects.requireNonNull(elements.get(n-1));}

@Override public int getChildCount(){return 1+elements.size();}

@Override public String toString(){StringBuilder sb=new StringBuilder();sb.append(path);sb.append("(");for(int i=0;i<elements.size();i++){if(i>0)sb.append(", ");sb.append(elements.get(i));}sb.append(")");return sb.toString();}

@Override public Type type(Services services){throw new UnsupportedOperationException();}}
