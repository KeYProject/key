/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.Name;
import org.key_project.logic.TerminalSyntaxElement;


/**
 * A schema variable that is used as placeholder for formulas.
 */
public final class FormulaSV extends JOperatorSV implements TerminalSyntaxElement {

    /**
     * @param name the name of the SchemaVariable
     * @param isRigid true iff this SV may only match rigid formulas
     */
    FormulaSV(Name name, boolean isRigid) {
        super(name, JavaDLTheory.FORMULA, isRigid, true);
    }

    @Override
    public String toString() {
        return toString("formula");
    }

    @Override
    public boolean isFormula() {
        return true;
    }

}
