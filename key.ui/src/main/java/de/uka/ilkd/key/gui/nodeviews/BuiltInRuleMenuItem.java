/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.rule.BuiltInRule;

public interface BuiltInRuleMenuItem {

    BuiltInRule connectedTo();

    boolean forcedApplication();

}
