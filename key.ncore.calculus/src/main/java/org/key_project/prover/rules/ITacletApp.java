/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.instantiation.SVInstantiations;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

public interface ITacletApp extends RuleApp {

    /// returns the taclet associated with this taclet application
    Taclet taclet();

    /**
     * returns the instantiations for the application of the Taclet at the specified position.
     *
     * @return the SVInstantiations needed to instantiate the Taclet
     */
    default SVInstantiations instantiations() {
        return matchConditions().getInstantiations();
    }

    @NonNull
    MatchResultInfo matchConditions();

    ImmutableList<AssumesFormulaInstantiation> assumesFormulaInstantiations();

    boolean assumesInstantionsComplete();

    /**
     * returns the variables that have not yet been instantiated and need to be instantiated to
     * apply the Taclet. (These are not all SchemaVariables like the one that appear only in the
     * addrule sections)
     *
     * @return ImmutableSet<SchemaVariable> with SchemaVariables that have not been instantiated yet
     */
    @NonNull
    ImmutableSet<SchemaVariable> uninstantiatedVars();
}
