/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a profile declaration in a KeY specification file.
 * Corresponds to: PROFILE name=string_value SEMI;
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class Profile extends BaseAstNode implements Declaration {
    private final String name;

    public Profile(Position position, String name) {
        super(position);
        this.name = name;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public String getName() {
        return name;
    }
}