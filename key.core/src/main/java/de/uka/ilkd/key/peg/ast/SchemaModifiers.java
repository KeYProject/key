/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents schema modifiers.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * schema_modifiers: LBRACKET opts = simple_ident_comma_list RBRACKET;
 * }</pre>
 */
@NullMarked
public class SchemaModifiers extends BaseAstNode {
    private final List<String> options;

    public SchemaModifiers(Position position, List<String> options) {
        super(position);
        this.options = options;
    }

    public List<String> getOptions() {
        return options;
    }
}
