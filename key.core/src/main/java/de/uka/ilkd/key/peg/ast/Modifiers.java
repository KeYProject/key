/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents modifiers for taclets.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * modifiers: LBRACKET ident+=simple_ident (COMMA ident+=simple_ident)* RBRACKET;
 * }</pre>
 */
@NullMarked
public class Modifiers extends BaseAstNode {
    private final List<String> modifierNames;

    public Modifiers(Position position, List<String> modifierNames) {
        super(position);
        this.modifierNames = modifierNames;
    }

    public List<String> getModifierNames() {
        return modifierNames;
    }
}