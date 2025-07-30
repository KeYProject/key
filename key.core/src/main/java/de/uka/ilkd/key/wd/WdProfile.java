/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.wd;

import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.BlockContractInternalRule;
import de.uka.ilkd.key.rule.BuiltInRule;

import org.key_project.util.collection.ImmutableList;

/**
 * @author Alexander Weigl
 * @version 1 (7/27/25)
 */
public class WdProfile extends JavaProfile {
    public static final WdProfile INSTANCE = new WdProfile();

    @Override
    protected ImmutableList<BuiltInRule> initBuiltInRules() {
        var javaRules = super.initBuiltInRules();
        return javaRules.map(it -> {
            if (it == BlockContractInternalRule.INSTANCE) {
                return WdBlockContractInternalRule.INSTANCE;
            }
            return it;
        });
    }
}
