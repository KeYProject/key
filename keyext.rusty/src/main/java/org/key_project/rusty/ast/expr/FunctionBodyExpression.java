/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.rusty.logic.op.ProgramVariable;

import org.jspecify.annotations.Nullable;

public record FunctionBodyExpression(@Nullable ProgramVariable resultVar,ProgramFunction fn,CallExpression call)implements Expr{@Override public Type type(Services services){return call.type(services);}

@Override public void visit(Visitor v){v.performActionOnFunctionBodyExpression(this);}

@Override public SyntaxElement getChild(int n){if(resultVar!=null){if(resultVar!=null)return resultVar;--n;};if(n==0)return call;throw new IndexOutOfBoundsException("Index: "+n);}

@Override public int getChildCount(){return 2;}

@Override public String toString(){var sb=new StringBuilder();if(resultVar!=null){sb.append(resultVar);sb.append(" = ");}return sb.append(call).append("@").toString();}

public BlockExpression getBody(){return fn.getBody();}}
