/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import java.awt.*;
import javax.swing.*;

import de.uka.ilkd.key.gui.fonticons.IconFactory;

/**
 * Tab component for {@link JTabbedPane} with a close button.
 *
 * @author lanzinger
 */
public class ClosableTabComponent extends JPanel {

    private static final long serialVersionUID = -7205139488676599833L;

    /**
     * Creates a new {@code ClosableTabComponent}.
     *
     * @param title the component's title.
     * @param closeAction the action to execute when the component is closed.
     */
    public ClosableTabComponent(String title, Action closeAction) {
        setOpaque(false);

        JLabel label = new JLabel(title);
        label.setBackground(UIManager.getColor("TabbedPane.background"));
        add(label);

        JButton button = new JButton(IconFactory.quit(16));
        button.setContentAreaFilled(false);
        button.setPreferredSize(new Dimension(16, 16));
        button.addActionListener(closeAction);
        add(button);
    }
}
