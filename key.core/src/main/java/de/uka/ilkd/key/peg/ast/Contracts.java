/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents contracts container.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * contracts: CONTRACTS LBRACE (rules_or_axioms SEMI)* RBRACE;
 * }</pre>
 */
@NullMarked
public class Contracts extends BaseAstNode {
    private final List<RulesOrAxioms> items;

    public Contracts(Position position, List<RulesOrAxioms> items) {
        super(position);
        this.items = items;
        for (RulesOrAxioms item : items) {
            setChildParent(item);
        }
    }

    public List<RulesOrAxioms> getItems() {
        return items;
    }
}