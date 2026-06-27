/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents add rules clause in taclet.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * add_rules: simple_ident_comma_list;
 * }</pre>
 */
@NullMarked
public class AddRules extends BaseAstNode {
    private final List<String> ruleNames;

    public AddRules(Position position, List<String> ruleNames) {
        super(position);
        this.ruleNames = ruleNames;
    }

    public List<String> getRuleNames() {
        return ruleNames;
    }
}