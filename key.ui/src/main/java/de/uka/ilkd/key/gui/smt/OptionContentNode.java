/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.smt;

import javax.swing.JComponent;
import javax.swing.tree.DefaultMutableTreeNode;

import org.jspecify.annotations.NullMarked;

/**
 * @author Mihai Herda, 2018
 */

@NullMarked
public class OptionContentNode extends DefaultMutableTreeNode {
    private static final long serialVersionUID = 1L;
    private final JComponent component;

    /**
     * Creates an option content node with the given title and component.
     *
     * <p>
     * The node sets its user object while the receiver is still under initialization (EISOP
     * initialization check); the title only materializes once the node is used in a tree after
     * construction, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public OptionContentNode(String title, JComponent component) {
        super();
        this.component = component;
        this.setUserObject(title);
    }

    public JComponent getComponent() {
        return component;
    }

}
