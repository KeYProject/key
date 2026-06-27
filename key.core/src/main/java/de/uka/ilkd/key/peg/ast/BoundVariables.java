/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents bound variables in quantifiers.
 * Corresponds to: var=one_bound_variable (COMMA var=one_bound_variable)* SEMI;
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class BoundVariables extends BaseAstNode {
    private final List<OneBoundVariable> variables;

    public BoundVariables(Position position,
                          List<OneBoundVariable> variables) {
        super(position);
        this.variables = variables;
        for (OneBoundVariable var : variables) {
            setChildParent(var);
        }
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public List<OneBoundVariable> getVariables() {
        return variables;
    }
}