/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;

//spotless:off
public record Path<R>(R res, ImmutableArray<PathSegment> segments) implements RustyProgramElement {
    @Override
    public @NonNull SyntaxElement getChild(int n) {
        return Objects.requireNonNull(segments.get(n));
    }

    @Override
    public int getChildCount() {
        return segments.size();
    }

    @Override
    public String toString() {
        var sb = new StringBuilder();
        for (int i = 0; i < segments.size(); i++) {
            if (i > 0) {
                sb.append("::");
            }
            sb.append(segments.get(i));
        }
        return sb.toString();
    }

    @Override
    public void visit(Visitor v) {

    }
}
//spotless:on