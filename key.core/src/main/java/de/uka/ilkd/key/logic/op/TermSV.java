/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.pp.Layouter;


/**
 * A schema variable that is used as placeholder for terms.
 */
public final class TermSV extends AbstractSV {

    /**
     * @param name the name of the schema variable
     * @param sort the sort of the schema variable
     * @param isRigid true iff this schema variable may only match rigid terms
     * @param isStrict boolean indicating if the schema variable is declared as strict forcing exact
     *        type match
     */
    TermSV(Name name, Sort sort, boolean isRigid, boolean isStrict) {
        super(name, sort, isRigid, isStrict);
        assert sort != Sort.FORMULA;
        assert sort != Sort.UPDATE;
    }

    @Override
    public String toString() {
        return toString(sort().toString() + " term");
    }

    @Override
    public void layout(Layouter<?> l) {
        l.print("\\schemaVar \\term ").print(sort().name().toString()).print(" ")
                .print(name().toString());
    }
}
