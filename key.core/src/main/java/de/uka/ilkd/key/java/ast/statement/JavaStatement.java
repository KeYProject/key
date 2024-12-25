/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.Statement;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Default implementation for non-terminal Java statements.
 */
public abstract class JavaStatement extends JavaNonTerminalProgramElement implements Statement {
    public JavaStatement() {
        this(null, null);
    }

    public JavaStatement(@Nullable PositionInfo pos) {
        super(pos);
    }

    public JavaStatement(@Nullable PositionInfo pi, @Nullable List<Comment> comments) {
        super(pi, comments);
    }
}
