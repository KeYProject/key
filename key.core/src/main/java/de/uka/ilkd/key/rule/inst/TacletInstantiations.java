/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.inst;


import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.util.collection.ImmutableMap;

/**
 * this class contains a Taclet together with its suggested instantiations.
 */
public class TacletInstantiations {

    /** the rule */
    private final Taclet rule;
    /** the instantations */
    private final ImmutableMap<SchemaVariable, Term> instantiations;

    public TacletInstantiations(Taclet rule, ImmutableMap<SchemaVariable, Term> instantiations) {
        this.rule = rule;
        this.instantiations = instantiations;
    }

    public Taclet taclet() {
        return rule;
    }

    public ImmutableMap<SchemaVariable, Term> instantiations() {
        return instantiations;
    }

    public String toString() {
        return "rule: " + taclet() + "; instantiation: " + instantiations();
    }


}
