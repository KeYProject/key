/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a variable expression (name and type).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * varexp: ident COLON keyjavatype;
 * }</pre>
 */
@NullMarked
public class Varexp extends BaseAstNode {
    private final String name;
    private final KeyJavaType type;

    public Varexp(Position position, String name, KeyJavaType type) {
        super(position);
        this.name = name;
        this.type = type;
    }

    public String getName() {
        return name;
    }

    public KeyJavaType getType() {
        return type;
    }
}