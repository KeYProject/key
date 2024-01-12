/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import javax.swing.JMenuItem;

import de.uka.ilkd.key.rule.BuiltInRule;


/**
 * equal to TacletMenuItem but for BuiltInRules
 */
class DefaultBuiltInRuleMenuItem extends JMenuItem implements BuiltInRuleMenuItem {

    /**
     *
     */
    private static final long serialVersionUID = 2104546363767367689L;
    private final BuiltInRule connectedTo;
    private final boolean forced;


    public DefaultBuiltInRuleMenuItem(String title, BuiltInRule connectedTo, boolean forced) {
        super(title);
        this.connectedTo = connectedTo;
        this.forced = forced;
    }

    public DefaultBuiltInRuleMenuItem(BuiltInRule connectedTo, boolean forced) {
        this(connectedTo.toString(), connectedTo, forced);
    }

    public DefaultBuiltInRuleMenuItem(BuiltInRule connectedTo) {
        this(connectedTo, false);
    }


    public BuiltInRule connectedTo() {
        return connectedTo;
    }

    @Override
    public boolean forcedApplication() {
        return forced;
    }

}
