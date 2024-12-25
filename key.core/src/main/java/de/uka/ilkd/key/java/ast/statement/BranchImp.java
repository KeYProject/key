/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.PositionInfo;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Branch.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class BranchImp extends JavaNonTerminalProgramElement implements Branch {
    public BranchImp() {
        this(null, null);
    }

    public BranchImp(@Nullable PositionInfo pi, @Nullable List<Comment> comments) {
        super(pi, comments);
    }
}
