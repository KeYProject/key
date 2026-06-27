/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a configuration key (simple identifier with dots).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * ckey: simple_ident_dots;
 * }</pre>
 */
@NullMarked
public class CKey extends BaseAstNode {
    private final String key;

    public CKey(Position position, String key) {
        super(position);
        this.key = key;
    }

    public String getKey() {
        return key;
    }
}