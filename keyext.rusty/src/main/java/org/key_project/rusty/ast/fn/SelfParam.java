/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.fn;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.ty.RustType;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public record SelfParam(boolean reference,boolean mut,@Nullable RustType ty)implements FunctionParam{@Override public void visit(Visitor v){v.performActionOnSelfParam(this);}

@Override public @NonNull SyntaxElement getChild(int n){
    if (n == 0) return ty;
    throw new IndexOutOfBoundsException(getClass() + " has 1 child");
}

@Override public int getChildCount(){return 1;}

@Override public RustType type(){
// TODO
return ty;}}
