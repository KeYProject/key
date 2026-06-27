/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a modality term (box/diamond).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * modality_term: (BOX | DIAMOND) program DOT term;
 * }</pre>
 */
@NullMarked
public class ModalityTerm extends BaseAstNode {
    private final boolean isBox;
    private final Term program;
    private final Term body;

    public ModalityTerm(Position position, boolean isBox, Term program, Term body) {
        super(position);
        this.isBox = isBox;
        this.program = program;
        this.body = body;
        setChildParent(program);
        setChildParent(body);
    }

    public boolean isBox() {
        return isBox;
    }

    public Term getProgram() {
        return program;
    }

    public Term getBody() {
        return body;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}