/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Represents a ruleset declaration.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * ruleset_decl: doc=DOC_COMMENT? name=simple_ident (COLON parent_rules+=simple_ident (COMMA parent_rules+=simple_ident)*)? SEMI;
 * }</pre>
 */
@NullMarked
public class RulesetDecl extends BaseAstNode {
    private final @Nullable String docComment;
    private final SimpleIdentDots name;
    private final List<SimpleIdentDots> parentRules;

    public RulesetDecl(Position position, @Nullable String docComment, SimpleIdentDots name, List<SimpleIdentDots> parentRules) {
        super(position);
        this.docComment = docComment;
        this.name = name;
        this.parentRules = parentRules;
        setChildParent(name);
        for (SimpleIdentDots p : parentRules) {
            setChildParent(p);
        }
    }

    public @Nullable String getDocComment() {
        return docComment;
    }

    public SimpleIdentDots getName() {
        return name;
    }

    public List<SimpleIdentDots> getParentRules() {
        return parentRules;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}