/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.Label;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public record InfiniteLoopExpression(@Nullable Label label,BlockExpression body)implements LoopExpression{@Override public void visit(Visitor v){v.performActionOnInfiniteLoop(this);}

@Override public @NonNull SyntaxElement getChild(int n){if(n==0&&label!=null)return label;if(n==0)return body;throw new IndexOutOfBoundsException("Infinite loop expression has only 1 child");}

@Override public int getChildCount(){return 1;}}
