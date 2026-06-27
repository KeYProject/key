/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents an elementary update term (location := value).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * elementary_update_term: location_term ASSIGN term;
 * }</pre>
 */
@NullMarked
public class ElementaryUpdateTerm extends BaseAstNode {
    private final LocationTerm location;
    private final Term value;

    public ElementaryUpdateTerm(Position position, LocationTerm location, Term value) {
        super(position);
        this.location = location;
        this.value = value;
        setChildParent(location);
        setChildParent(value);
    }

    public LocationTerm getLocation() {
        return location;
    }

    public Term getValue() {
        return value;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}