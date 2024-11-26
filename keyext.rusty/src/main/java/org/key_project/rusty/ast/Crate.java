/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;


import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.fn.Function;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

public class Crate implements RustyProgramElement {
    private final Mod topMod;

    public Crate(Mod topMod) {
        this.topMod = topMod;
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {
            return topMod;
        }
        throw new IndexOutOfBoundsException("Crate has only 1 child");
    }

    @Override
    public String toString() {
        return topMod.toString();
    }

    @Override
    public void visit(Visitor v) {
        throw new RuntimeException("Shouldn't be called");
    }

    public Mod getTopMod() {
        return topMod;
    }

    public Function getVerificationTarget() {
        return (Function) topMod.getItems()
                .filter(i -> i instanceof Function fn
                        && fn.name().toString().equals(Context.TMP_FN_NAME))
                .stream().findAny().get();
    }
}
