/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.proof;

/**
 * This listener is notified whenever a rule is applied in an ongoing proof.
 */
@FunctionalInterface
public interface RuleAppListener {

    /**
     * Invoked when a rule has been applied.
     *
     * @param e the proof event containing the rule application.
     */
    void ruleApplied(de.uka.ilkd.key.proof.ProofEvent e);
}
