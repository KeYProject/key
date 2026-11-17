/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.strategy.costbased.RuleAppCost;

/// Interface for collecting `RuleApp`s, together with their assigned cost. This interface
/// is used in the signature of the method `Strategy.instantiateApp`
public interface RuleAppCostCollector {
    void collect(RuleApp app, RuleAppCost cost);
}
