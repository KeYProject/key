/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a configuration key-value pair.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * ckv: ckey EQUALS cvalue NEWLINE;
 * }</pre>
 */
@NullMarked
public class CKV extends BaseAstNode {
    private final CKey key;
    private final CValue value;

    public CKV(Position position, CKey key, CValue value) {
        super(position);
        this.key = key;
        this.value = value;
        setChildParent(key);
        setChildParent(value);
    }

    public CKey getKey() {
        return key;
    }

    public CValue getValue() {
        return value;
    }
}