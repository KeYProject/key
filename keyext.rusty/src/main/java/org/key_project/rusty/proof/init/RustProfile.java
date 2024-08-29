/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.init;


import org.key_project.rusty.proof.io.RuleSourceFactory;
import org.key_project.rusty.rule.BuiltInRule;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

public class RustProfile implements Profile {
    public static final String NAME = "Rust Profile";

    public static RustProfile defaultInstance;

    // maybe move these fields to abstract parent AbstractProfile
    private final RuleCollection standardRules;

    protected RustProfile(String standardRuleFilename) {
        standardRules = new RuleCollection(
            RuleSourceFactory.fromDefaultLocation(standardRuleFilename), initBuiltInRules());
    }

    public RustProfile() {
        this("standardRustRules.key");
    }


    @Override
    public RuleCollection getStandardRules() {
        return standardRules;
    }

    @Override
    public String name() {
        return NAME;
    }

    protected ImmutableList<BuiltInRule> initBuiltInRules() {
        return ImmutableSLList.nil();
    }
}
