/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a preferences/settings declaration in a KeY specification file.
 * Corresponds to: KEYSETTINGS (LBRACE s=string_value? RBRACE | c=cvalue);
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public class Preferences extends BaseAstNode implements Declaration {
    private final @Nullable String stringValue;
    private final @Nullable CValue cvalue;

    public Preferences(Position position,
                       @Nullable String stringValue, @Nullable CValue cvalue) {
        super(position);
        this.stringValue = stringValue;
        this.cvalue = cvalue;
        setChildParent(cvalue);
    }

    @Override
    public <T> T accept(AstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public @Nullable String getStringValue() {
        return stringValue;
    }

    public @Nullable CValue getCvalue() {
        return cvalue;
    }
}