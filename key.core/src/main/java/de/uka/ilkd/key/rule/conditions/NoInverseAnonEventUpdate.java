/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

public class NoInverseAnonEventUpdate extends VariableConditionAdapter {

    private final SchemaVariable updateSV;

    public NoInverseAnonEventUpdate(SchemaVariable var) {
        this.updateSV = var;
    }

    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
            SVInstantiations instMap, Services services) {

        if (var != updateSV) {
            return true;
        }

        final Term inst = (Term) instMap.getInstantiation(var);

        final Term update = (Term) inst;
        if (update.sort() == Sort.UPDATE) {
            return !checkForInverseAnonEvent(update);
        }

        return false;
    }

    private boolean checkForInverseAnonEvent(Term update) {

        final Operator op = update.op();

        if (op instanceof ElementaryUpdate ||
                op == UpdateJunctor.SKIP || op == EventUpdate.SINGLETON
                || op == AnonEventUpdate.SINGLETON || op == InverseEventUpdate.SINGLETON) {
            return false;
        } else if (op == InverseAnonEventUpdate.SINGLETON) {
            return true;
        } else if (op == UpdateJunctor.PARALLEL_UPDATE || op == UpdateJunctor.SEQUENTIAL_UPDATE) {
            return (checkForInverseAnonEvent(update.sub(0))
                    || checkForInverseAnonEvent(update.sub(1)));
        } else if (op == UpdateApplication.UPDATE_APPLICATION) {
            return checkForInverseAnonEvent(update.sub(1));
        }

        Debug.fail("Forgotten update operator", op.getClass());
        return true;
    }

    public String toString() {
        return "\\noInverseAnonEventUpdate(" + updateSV.name() + ")";
    }

}
