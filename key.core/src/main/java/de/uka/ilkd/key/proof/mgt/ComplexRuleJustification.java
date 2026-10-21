/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.mgt;

import org.key_project.logic.LogicServices;
import org.key_project.prover.rules.RuleApp;

public interface ComplexRuleJustification extends RuleJustification {

    RuleJustification getSpecificJustification(RuleApp app, LogicServices services);

}
