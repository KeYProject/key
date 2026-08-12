/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.Name;
import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.logic.sort.Sort;

/**
 * Schema variable that is instantiated with fresh Skolem constants. At the moment, such schema
 * variables have to be accompanied by a "NewDependingOn" varcond, although with the removal of the
 * meta variable mechanism, this would no longer really be necessary.
 */
public final class SkolemTermSV extends JOperatorSV implements TerminalSyntaxElement {

    /** whether the constants created for this schema variable are definitional symbols */
    private final boolean definitional;

    /**
     * Creates a new schema variable that is used as placeholder for skolem terms.
     *
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the SchemaVariable and the matched type allowed to match a list of
     *        program constructs
     * @param definitional whether the created constants are definitional symbols, declared as
     *        {@code \skolemTerm[definitional]}
     */
    SkolemTermSV(Name name, Sort sort, boolean definitional) {
        super(name, sort, true, false);
        this.definitional = definitional;
        assert sort != JavaDLTheory.UPDATE;
    }

    /** @return whether the constants created for this schema variable are definitional symbols */
    public boolean isDefinitional() {
        return definitional;
    }

    @Override
    public boolean isSkolemTerm() {
        return true;
    }

    @Override
    public String toString() {
        return toString(sort() + " skolem term");
    }
}
