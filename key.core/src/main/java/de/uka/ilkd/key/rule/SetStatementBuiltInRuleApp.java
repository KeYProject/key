/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.Objects;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.util.collection.ImmutableList;

/**
 * The rule application for {@link de.uka.ilkd.key.java.statement.SetStatement}
 *
 * @author Julian Wiesler
 */
public class SetStatementBuiltInRuleApp extends AbstractBuiltInRuleApp {
    /**
     * @param rule the rule being applied
     * @param occurrence the position at which the rule is applied
     */
    public SetStatementBuiltInRuleApp(BuiltInRule rule, PosInOccurrence occurrence) {
        super(rule, Objects.requireNonNull(occurrence, "rule application needs a position"), null);
        if (!(rule instanceof SetStatementRule)) {
            throw new IllegalArgumentException(String.format(
                "can only create an application for SetStatementRule, not for %s", rule));
        }
    }

    @Override
    public SetStatementBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return new SetStatementBuiltInRuleApp(rule(), newPos);
    }

    @Override
    public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        // XXX: This is overridden in all subclasses to allow making ifInsts final
        // when all usages of setIfInsts are corrected to use the result.
        // Then a new instance has to be returned here.
        setMutable(ifInsts);
        return this;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        return this;
    }
}
