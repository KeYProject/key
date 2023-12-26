/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder.branchlabel;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.TacletApp;


/**
 * A {@code BranchNamingFunction} is a function that returns a string that is inserted in the
 * branch name of a rule application.
 * <br>
 * It allows you to create branch labels dynamically based the term structure, and other information
 * of the rule application. Introduced for supporting branch labels based on term label
 * {@code name}.
 *
 * @author Alexander Weigl
 * @version 1 (1/15/22)
 */
public interface BranchNamingFunction {
    String getName(Services services, SequentChangeInfo currentSequent,
            TacletApp tacletApp, MatchConditions matchConditions);
}
