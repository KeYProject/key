/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Represents a choice with optional options.
 * Corresponds to the grammar rule:
 * <pre>{@code
 * choice: maindoc+=DOC_COMMENT* category=IDENT (COLON LBRACE optionDecl (COMMA optionDecl)* RBRACE)?;
 * }</pre>
 */
@NullMarked
public class Choice extends BaseAstNode {
    private final List<String> docComments;
    private final String category;
    private final @Nullable List<String> optionDecls;

    public Choice(Position position, List<String> docComments, String category, @Nullable List<String> optionDecls) {
        super(position);
        this.docComments = docComments;
        this.category = category;
        this.optionDecls = optionDecls;
    }

    public List<String> getDocComments() {
        return docComments;
    }

    public String getCategory() {
        return category;
    }

    public @Nullable List<String> getOptionDecls() {
        return optionDecls;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}