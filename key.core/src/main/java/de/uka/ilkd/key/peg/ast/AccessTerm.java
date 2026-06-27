/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents an access term (for information flow control).
 * Corresponds to the grammar rule:
 * <pre>{@code
 * access_term: ACCESS location_term;
 * }</pre>
 */
@NullMarked
public class AccessTerm extends BaseAstNode {
    private final LocationTerm location;

    public AccessTerm(Position position, LocationTerm location) {
        super(position);
        this.location = location;
        setChildParent(location);
    }

    public LocationTerm getLocation() {
        return location;
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }
}