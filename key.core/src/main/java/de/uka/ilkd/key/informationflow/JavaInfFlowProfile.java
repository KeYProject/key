/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow;

import de.uka.ilkd.key.informationflow.rule.InfFlowBlockContractInternalRule;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.*;

import org.key_project.util.collection.ImmutableList;

/**
 * This profile sets up KeY for verification of JavaCard programs.
 */
public class JavaInfFlowProfile extends JavaProfile {
    public static final String NAME = "Java InfFlow Profile";

    @Override
    protected ImmutableList<BuiltInRule> initBuiltInRules() {
        var rules = super.initBuiltInRules();
        return rules.map(it -> {
            if (it == BlockContractInternalRule.INSTANCE) {
                return InfFlowBlockContractInternalRule.INSTANCE;
            }
            return it;
        }).filter(it -> it != BlockContractExternalRule.INSTANCE);
    }
}
