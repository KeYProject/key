/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.pat;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.Identifier;

import org.jspecify.annotations.NonNull;

public class IdentPattern implements Pattern, Named {
    private final boolean reference;
    private final boolean mutable;
    private final Identifier ident;

    public IdentPattern(boolean reference, boolean mutable, Identifier ident) {
        this.reference = reference;
        this.mutable = mutable;
        this.ident = ident;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {
            return ident;
        }
        throw new IndexOutOfBoundsException("IdentPattern has only one child");
    }

    public boolean isMutable() {
        return mutable;
    }

    public boolean isReference() {
        return reference;
    }

    @Override
    public @NonNull Name name() {
        return ident.name();
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public String toString() {
        if (mutable)
            return "mut " + ident.toString();
        return ident.toString();
    }
}
