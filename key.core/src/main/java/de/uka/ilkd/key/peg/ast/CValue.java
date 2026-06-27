/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a configuration value (string).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * cvalue: STRING;
 * }</pre>
 */
@NullMarked
public class CValue extends BaseAstNode {
    private final String value;

    public CValue(Position position, String value) {
        super(position);
        this.value = value;
    }

    public String getValue() {
        return value;
    }
}