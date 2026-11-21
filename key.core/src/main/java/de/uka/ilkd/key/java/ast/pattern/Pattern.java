/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.pattern;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.PositionInfo;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;

/**
 * A Java pattern (JLS 14.30.1), i.e. a type pattern or a record pattern.
 *
 * <p>
 * Patterns appear in {@link de.uka.ilkd.key.java.ast.expression.operator.InstanceofPattern
 * instanceof} expressions and declare the local variables that are bound when the pattern matches.
 * A record pattern may contain further patterns, so patterns form a tree.
 *
 * @author Alexander Weigl
 */
@NullMarked
public abstract class Pattern extends JavaNonTerminalProgramElement {

    protected Pattern() {
    }

    protected Pattern(ExtList children) {
        super(children);
    }

    protected Pattern(PositionInfo pi, List<Comment> comments) {
        super(pi, comments);
    }
}
