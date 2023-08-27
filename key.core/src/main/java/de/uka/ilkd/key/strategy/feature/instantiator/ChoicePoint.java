/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature.instantiator;

import java.util.Iterator;

import de.uka.ilkd.key.rule.RuleApp;

/**
 * Interface encapsulating points during the evaluation of a feature term where it is either
 * possible to take different branches, or where the feature has to change the rule application in
 * question (e.g. by instantiation schema variables).
 */
public interface ChoicePoint {

    /**
     * Obtain the branches that can be taken at this point.
     *
     * @param oldApp the current rule application, which can already have been modified by earlier
     *        <code>ChoicePoint</code>s
     * @return an iterator over the branches of the <code>ChoicePoint</code>
     */
    Iterator<CPBranch> getBranches(RuleApp oldApp);

}
