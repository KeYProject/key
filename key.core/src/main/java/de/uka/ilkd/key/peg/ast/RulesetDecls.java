/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.List;

/**
 * Represents ruleset declarations.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * ruleset_decls: RULESET LBRACE ruleset_decl* RBRACE;
 * }</pre>
 */
@NullMarked
public class RulesetDecls extends BaseAstNode {
    private final List<RulesetDecl> decls;

    public RulesetDecls(Position position, List<RulesetDecl> decls) {
        super(position);
        this.decls = decls;
        for (RulesetDecl d : decls) {
            setChildParent(d);
        }
    }

    public List<RulesetDecl> getDecls() {
        return decls;
    }
}