/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents a proof declaration in a KeY specification file.
 * Corresponds to: PROOF EOF;
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class Proof extends BaseAstNode implements Declaration {
    public Proof(Position position) {
        super(position);
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}