/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.pat;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.collection.ImmutableArray;

//spotless:off
public record AltPattern(ImmutableArray<Pattern> alternatives) implements Pattern {
    @Override
    public SyntaxElement getChild(int n) {
        return null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnAltPattern(this);
    }
}
//spotless:on