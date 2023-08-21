/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

/**
 * An {@link AutomatedRuleApplicationManager} based on delegation.
 *
 * @author Dominic Steinhoefel
 */
public interface DelegationBasedAutomatedRuleApplicationManager
        extends AutomatedRuleApplicationManager {
    /**
     * @return The delegate.
     */
    AutomatedRuleApplicationManager getDelegate();
}
