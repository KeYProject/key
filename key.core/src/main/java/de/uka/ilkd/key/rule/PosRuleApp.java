/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.PosInOccurrence;

/**
 * Interface for rule applications with associated position information.
 *
 * @author Arne Keller
 */
public interface PosRuleApp {
    /**
     * @return the position the rule was applied on
     */
    PosInOccurrence posInOccurrence();
}
