/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.strategy;

/**
 *
 */
public interface RuleAppCost extends Comparable<RuleAppCost> {

    public int compareTo(RuleAppCost o);

    /**
     * Add the given costs to the costs that are represented by this object
     */
    RuleAppCost add(RuleAppCost cost2);

}
