/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.pat;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.Identifier;
import org.key_project.rusty.ast.visitor.Visitor;

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

    @Override
    public void visit(Visitor v) {
        v.performActionOnIdentPattern(this);
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this) {
            return true;
        }
        if (obj == null || obj.getClass() != this.getClass()) {
            return false;
        }
        final var other = (IdentPattern) obj;
        return reference == other.reference && mutable == other.mutable
                && ident.equals(other.ident);
    }

    @Override
    public int hashCode() {
        int hashcode = 5;
        hashcode = 31 * hashcode + Boolean.hashCode(reference);
        hashcode = 31 * hashcode + Boolean.hashCode(mutable);
        hashcode = 31 * hashcode + ident.hashCode();
        return hashcode;
    }
}
