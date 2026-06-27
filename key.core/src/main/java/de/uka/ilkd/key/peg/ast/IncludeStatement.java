/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Represents an include statement in a KeY specification file.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_include_statement: (INCLUDE | INCLUDELDTS) one_include (COMMA one_include)* SEMI;
 * }</pre>
 */
@NullMarked
public class IncludeStatement extends BaseAstNode {
    private final boolean isLdt;
    private final List<OneInclude> includes;

    public IncludeStatement(Position position, boolean isLdt, List<OneInclude> includes) {
        super(position);
        this.isLdt = isLdt;
        this.includes = includes;
        for (OneInclude inc : includes) {
            setChildParent(inc);
        }
    }

    public boolean isLdt() {
        return isLdt;
    }

    public List<OneInclude> getIncludes() {
        return includes;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
