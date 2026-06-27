/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Represents a sort identifier.
 * Corresponds to: id=simple_ident_dots formal_sort_args? (EMPTYBRACKETS)*;
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class SortId extends BaseAstNode {
    private final List<String> parts;
    private final @Nullable FormalSortArgs formalArgs;
    private final int arrayDimensions;

    public SortId(Position position,
                  List<String> parts, @Nullable FormalSortArgs formalArgs, int arrayDimensions) {
        super(position);
        this.parts = parts;
        this.formalArgs = formalArgs;
        this.arrayDimensions = arrayDimensions;
        setChildParent(formalArgs);
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public List<String> getParts() {
        return parts;
    }

    public @Nullable FormalSortArgs getFormalArgs() {
        return formalArgs;
    }

    public int getArrayDimensions() {
        return arrayDimensions;
    }

    public String getFullName() {
        return String.join(".", parts);
    }
}