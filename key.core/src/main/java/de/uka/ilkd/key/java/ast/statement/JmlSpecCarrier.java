/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.speclang.JmlStatementSpec;

import org.jspecify.annotations.Nullable;

/**
 * Marker interface for JML statements ({@link JmlAssert}, {@link SetStatement}) that carry a
 * translated {@link JmlStatementSpec} directly on the AST node.
 * <p>
 * The spec (translated terms + program-variable scope) used to live in the
 * {@code SpecificationRepository}'s global identity map; it is now attached to the statement node
 * itself so that the repository can be deleted (see the JMLtk front-end rewrite project).
 */
public interface JmlSpecCarrier {

    /** Returns the translated specification of this statement, or {@code null} if not yet translated. */
    @Nullable JmlStatementSpec getSpec();

    /** Attaches the translated specification to this statement. */
    void setSpec(@Nullable JmlStatementSpec spec);
}
