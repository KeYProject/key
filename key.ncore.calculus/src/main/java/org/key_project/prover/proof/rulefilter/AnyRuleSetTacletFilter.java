/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.proof.rulefilter;

import org.key_project.prover.rules.Taclet;

/// Filter that selects taclets that belong to at least one rule set, i.e. taclets that can be
/// applied automatically.
public class AnyRuleSetTacletFilter extends TacletFilter {

    private AnyRuleSetTacletFilter() {
    }

    /// @return true iff <code>taclet</code> should be included in the result
    public boolean filter(Taclet taclet) {
        return !taclet.getRuleSets().isEmpty();
    }

    public final static TacletFilter INSTANCE = new AnyRuleSetTacletFilter();
}
