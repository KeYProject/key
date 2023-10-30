/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.pp.Layouter;

/**
 * Schema variable that is instantiated with fresh Skolem constants. At the moment, such schema
 * variables have to be accompanied by a "NewDependingOn" varcond, although with the removal of the
 * meta variable mechanism, this would no longer really be necessary.
 */
public final class SkolemTermSV extends AbstractSV {

    /**
     * Creates a new schema variable that is used as placeholder for skolem terms.
     *
     * @param name the Name of the SchemaVariable
     * @param sort the Sort of the SchemaVariable and the matched type allowed to match a list of
     *        program constructs
     */
    SkolemTermSV(Name name, Sort sort) {
        super(name, sort, true, false);
        assert sort != Sort.UPDATE;
    }

    @Override
    public String toString() {
        return toString(sort().toString() + " skolem term");
    }

    @Override
    public void layout(Layouter<?> l) {
        l.print("\\schemaVar ");
        if (sort() == Sort.FORMULA) {
            l.print("\\skolemFormula");
        } else {
            l.print("\\skolemTerm ").print(sort().name().toString());
        }
        l.print(" ").print(name().toString());
    }
}
