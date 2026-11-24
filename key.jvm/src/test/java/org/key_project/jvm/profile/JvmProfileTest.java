/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm.profile;

import de.uka.ilkd.key.proof.init.ProofInitServiceUtil;
import de.uka.ilkd.key.rule.UseOperationContractRule;

import org.key_project.jvm.rule.GotoRestoreRule;
import org.key_project.jvm.rule.GotoSpliceRule;
import org.key_project.jvm.rule.IfLiteralRule;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Smoke test for the M0 scaffolding: the {@link JvmProfile} must be selectable by name through the
 * {@link DefaultProfileResolver} service loading, and its built-in rules must include the JVM
 * rules with {@link UseOperationContractRule} kept as the first element (ProofMgt invariant).
 */
class JvmProfileTest {

    @Test
    void profileIsRegisteredUnderId() {
        // ProofInitServiceUtil resolves by name from META-INF/services/...DefaultProfileResolver.
        var profile = ProofInitServiceUtil.getDefaultProfile(JvmProfile.PROFILE_ID);
        assertThat(profile).isSameAs(JvmProfile.INSTANCE);
    }

    @Test
    void builtInRulesAppendTheJvmRulesKeepingContractRuleFirst() {
        var profile = ProofInitServiceUtil.getDefaultProfile(JvmProfile.PROFILE_ID);
        assertThat(profile).isNotNull();

        var rules = profile.getStandardRules().standardBuiltInRules();

        assertThat(rules).contains(GotoSpliceRule.INSTANCE, GotoRestoreRule.INSTANCE,
            IfLiteralRule.INSTANCE);
        assertThat(rules.head()).isSameAs(UseOperationContractRule.INSTANCE);
    }

}
