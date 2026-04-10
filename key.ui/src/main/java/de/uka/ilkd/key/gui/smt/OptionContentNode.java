/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.smt;

import javax.swing.JComponent;
import javax.swing.tree.DefaultMutableTreeNode;

/**
 * @author Mihai Herda, 2018
 */

public class OptionContentNode extends DefaultMutableTreeNode {
    private static final long serialVersionUID = 1L;
    private final JComponent component;

    public OptionContentNode(String title, JComponent component) {
        super();
        this.component = component;
        this.setUserObject(title);
    }

    public JComponent getComponent() {
        return component;
    }

}
