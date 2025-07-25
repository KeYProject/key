/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.proof.rulefilter;


import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.Taclet;

/// Interface for filtering a list of TacletApps, for example to choose only taclets for interactive
/// application or taclets belonging to some given heuristics.
public abstract class TacletFilter implements RuleFilter {
    /// Trival TacletFilter that always returns true;
    public static final TacletFilter TRUE = new TacletFilterTrue();

    @Override
    public boolean filter(Rule rule) {
        if (rule instanceof Taclet taclet) {
            return filter(taclet);
        }
        return false;
    }

    /// @return true iff <code>taclet</code> should be included in the result
    protected abstract boolean filter(Taclet taclet);

    /// Trival TacletFilter that always returns true;
    static class TacletFilterTrue extends TacletFilter {
        protected boolean filter(Taclet taclet) {
            return true;
        }
    }
}
