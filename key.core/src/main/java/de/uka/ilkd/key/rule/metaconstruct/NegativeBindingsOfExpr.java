/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ast.ProgramElement;

/**
 * The negative binding meta construct {@code #negBinding}: expands a guard expression into the
 * declarations of the pattern variables that are definitely bound if the expression evaluates to
 * {@code false}.
 */
@TransformerMeta(name = "#negBinding")
public final class NegativeBindingsOfExpr extends BindingsOfExpr {

    /**
     * @param body the schema variable holding the guard expression, e.g. {@code #nse}
     */
    public NegativeBindingsOfExpr(ProgramElement body) {
        super("#negBinding", body, false);
    }
}
