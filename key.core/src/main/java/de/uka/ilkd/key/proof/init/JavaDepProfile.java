/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.loopinvgen.NestedLoopUsecaseRule;
import de.uka.ilkd.key.loopinvgen.RelaxedShiftUpdateRule;
import de.uka.ilkd.key.loopinvgen.ShiftUpdateRule;
import de.uka.ilkd.key.rule.BuiltInRule;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Java profile for dependences verification
 */
public class JavaDepProfile extends JavaProfile {

    public static final String NAME = "Java with Dependencies Profile";

    public JavaDepProfile() {
        super("standardRules-dependencies.key");
    }

    @Override
    protected ImmutableList<BuiltInRule> initBuiltInRules() {
        return ImmutableSLList.<BuiltInRule>nil().prepend(ShiftUpdateRule.SHIFT_RULE)
                .prepend(RelaxedShiftUpdateRule.RELAXED_SHIFT_RULE)
                .prepend(NestedLoopUsecaseRule.NESTED_LOOP_USECASE_RUlE)
                .prepend(super.initBuiltInRules());
    }

    @Override
    public String name() {
        return NAME;
    }

}
