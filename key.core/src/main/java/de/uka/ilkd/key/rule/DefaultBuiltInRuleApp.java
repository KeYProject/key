/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;


import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;

/**
 * this class represents an application of a built-in rule application
 */
@NullMarked
public class DefaultBuiltInRuleApp<T extends BuiltInRule> extends AbstractBuiltInRuleApp<T> {

    public DefaultBuiltInRuleApp(T builtInRule, PosInOccurrence pio) {
        super(builtInRule, pio);
    }


    public DefaultBuiltInRuleApp(T builtInRule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts) {
        super(builtInRule, pio, ifInsts);
    }

    @Override
    public DefaultBuiltInRuleApp<T> replacePos(PosInOccurrence newPos) {
        return new DefaultBuiltInRuleApp<>(builtInRule, newPos, ifInsts);
    }

    @Override
    public DefaultBuiltInRuleApp<T> tryToInstantiate(Goal goal) {
        return this;
    }

    @Override
    public DefaultBuiltInRuleApp<T> setAssumesInsts(
            ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
        // return new DefaultBuiltInRuleApp(builtInRule, pio, ifInsts);
    }

}
