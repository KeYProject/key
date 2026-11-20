/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm.rule;

import java.util.Objects;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

/**
 * A minimal, reusable rule application for the JVM built-in rules. The rules are applied at the
 * top-level succedent and keep no instantiation state, so a single shared app class suffices for
 * M0/M1.
 */
public final class JvmBuiltInRuleApp extends AbstractBuiltInRuleApp<BuiltInRule> {

    public JvmBuiltInRuleApp(BuiltInRule rule, PosInOccurrence occurrence) {
        super(rule, Objects.requireNonNull(occurrence, "rule application needs a position"), null);
    }

    @Override
    public JvmBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return new JvmBuiltInRuleApp(rule(), newPos);
    }

    @Override
    public IBuiltInRuleApp setAssumesInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public JvmBuiltInRuleApp tryToInstantiate(Goal goal) {
        return this;
    }
}
