/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.SyntaxElement;

public class NoEventUpdate extends VariableConditionAdapter {

    private final SchemaVariable updateSV;

    public NoEventUpdate(SchemaVariable var) {
        this.updateSV = var;
    }

    @Override
    public boolean check(SchemaVariable var, SyntaxElement instCandidate,
            SVInstantiations instMap, Services services) {

        if (var != updateSV) {
            return true;
        }

        final Term inst = (Term) instMap.getInstantiation(var);

        final Term update = (Term) inst;
        if (update.sort() == JavaDLTheory.UPDATE) {
            return !checkForEvent(update);
        }

        return false;
    }

    private boolean checkForEvent(Term update) {

        final Operator op = update.op();

        if (op instanceof ElementaryUpdate || op == UpdateJunctor.SKIP
                || op == InverseEventUpdate.SINGLETON || op == AnonEventUpdate.SINGLETON
                || op == InverseAnonEventUpdate.SINGLETON) {
            return false;
        } else if (op == EventUpdate.SINGLETON) {
            return true;
        } else if (op == UpdateJunctor.PARALLEL_UPDATE || op == UpdateJunctor.SEQUENTIAL_UPDATE) {
            return (checkForEvent(update.sub(0)) || checkForEvent(update.sub(1)));
        } else if (op == UpdateApplication.UPDATE_APPLICATION) {
            return checkForEvent(update.sub(1));
        }
        Debug.fail("Forgotten update operator", op.getClass());
        return true;
    }

    public String toString() {
        return "\\noEventUpdate(" + updateSV.name() + ")";
    }

}
