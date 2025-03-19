/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class NoDependenceLDT extends VariableConditionAdapter {

    private final SchemaVariable dependenceSV;

    public NoDependenceLDT(SchemaVariable var) {
        this.dependenceSV = var;
    }

    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate, SVInstantiations instMap,
            Services services) {
        if (var != dependenceSV) {
            return true;
        }
        final Term inst = (Term) instMap.getInstantiation(var);

        if (inst instanceof DependenciesLDT) {
            return false;
        }
        return true;
    }


    public String toString() {
        return "\\noDependenceLDT(" + dependenceSV.name() + ")";
    }
}
