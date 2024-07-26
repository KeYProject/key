/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.SyntaxElement;

import org.jspecify.annotations.NonNull;

public record Identifier(Name name) implements Named, RustyProgramElement {

    @Override
    public @NonNull Name name() {
        return name;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Identifier has no children");
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public String toString() {
        return name().toString();
    }
}
