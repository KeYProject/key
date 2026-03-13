/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature.instantiator;

import org.key_project.prover.rules.RuleApp;

/// One branch of a <code>ChoicePoint</code>. An object of this interface will be notified each time
/// the <code>BackTrackingManager</code> decides to take this branch, and can be asked for the
/// current rule application.
public interface CPBranch {

    /// Invoked by branch manager when this branch of a choice point has been chosen
    void choose();

    /// @return the updated <code>RuleApp</code> that results when this branch of a choice point has
    /// been chosen
    RuleApp getRuleAppForBranch();

}
