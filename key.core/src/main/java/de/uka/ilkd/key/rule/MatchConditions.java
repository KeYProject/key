/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.RenameTable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.op.QuantifiableVariable;

import org.jspecify.annotations.NonNull;


/**
 * Simple container class containing the information resulting from a Taclet.match-call
 */
public class MatchConditions extends org.key_project.prover.rules.instantiation.MatchConditions {

    public static final MatchConditions EMPTY_MATCHCONDITIONS =
        new MatchConditions(SVInstantiations.EMPTY_SVINSTANTIATIONS, RenameTable.EMPTY_TABLE);

    private final RenameTable renameTable;

    public MatchConditions() {
        super(SVInstantiations.EMPTY_SVINSTANTIATIONS);
        this.renameTable = RenameTable.EMPTY_TABLE;
    }

    public MatchConditions(@NonNull SVInstantiations p_instantiations,
            @NonNull RenameTable p_renameTable) {
        super(p_instantiations);
        assert p_instantiations != null;
        assert p_renameTable != null;
        renameTable = p_renameTable;
    }

    @Override
    public SVInstantiations getInstantiations() {
        return (SVInstantiations) instantiations;
    }

    @Override
    public MatchConditions setInstantiations(
            org.key_project.prover.rules.instantiation.SVInstantiations p_instantiations) {
        if (instantiations == p_instantiations) {
            return this;
        } else {
            return new MatchConditions((SVInstantiations) p_instantiations, renameTable);
        }
    }

    public MatchConditions extendRenameTable() {
        return new MatchConditions((SVInstantiations) instantiations, renameTable.extend());
    }

    public MatchConditions addRenaming(QuantifiableVariable q1, QuantifiableVariable q2) {
        return new MatchConditions((SVInstantiations) instantiations, renameTable.assign(q1, q2));
    }

    public RenameTable renameTable() {
        return renameTable;
    }

    public MatchConditions shrinkRenameTable() {
        return new MatchConditions((SVInstantiations) instantiations, renameTable.parent());
    }


}
