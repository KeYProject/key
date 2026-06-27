/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a single include (absolute or relative file).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * one_include: absfile=IDENT | relfile=string_value;
 * }</pre>
 */
@NullMarked
public class OneInclude extends BaseAstNode {
    private final String value;
    private final boolean isAbsolute;

    public OneInclude(Position position, String value, boolean isAbsolute) {
        super(position);
        this.value = value;
        this.isAbsolute = isAbsolute;
    }

    public String getValue() {
        return value;
    }

    public boolean isAbsolute() {
        return isAbsolute;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
