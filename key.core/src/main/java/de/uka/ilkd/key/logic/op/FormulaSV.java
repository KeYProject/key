/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.pp.Layouter;


/**
 * A schema variable that is used as placeholder for formulas.
 */
public final class FormulaSV extends AbstractSV {

    /**
     * @param name the name of the SchemaVariable
     * @param isRigid true iff this SV may only match rigid formulas
     */
    FormulaSV(Name name, boolean isRigid) {
        super(name, Sort.FORMULA, isRigid, true);
    }

    @Override
    public String toString() {
        return toString("formula");
    }

    @Override
    public void layout(Layouter<?> layouter) {
        layouter.print("\\schemaVar \\formula ").print(name().toString());
    }
}
