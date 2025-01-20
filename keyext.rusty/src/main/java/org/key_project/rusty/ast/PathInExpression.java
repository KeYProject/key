/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast;

import java.util.Objects;
import java.util.stream.Collectors;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;

// spotless:off
public record PathInExpression(ImmutableArray<PathExprSegment> segments) implements RustyProgramElement {
    @Override
    public void visit(Visitor v) {
        v.performActionOnPathInExpression(this);
    }

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
        return segments.stream().map(PathExprSegment::toString).collect(Collectors.joining("::"));
    }
}
//spotless:on
