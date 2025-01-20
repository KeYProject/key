/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import javax.swing.JPanel;

/**
 * Creates the layout for SequentViews.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
class SequentViewPanel extends JPanel {

    private static final long serialVersionUID = -4052156449188977483L;

    protected SequentViewPanel(SequentView sequentView) {

        setLayout(new GridBagLayout());
        setBackground(sequentView.getBackground());

        GridBagConstraints gbc = new GridBagConstraints();

        gbc.fill = GridBagConstraints.HORIZONTAL;
        gbc.gridx = 1;
        gbc.gridy = 0;
        gbc.weightx = 1.0;
        gbc.weighty = 0.0;
        add(javax.swing.Box.createGlue(), gbc);

        gbc.insets = new Insets(0, 0, 0, 0);
        gbc.fill = GridBagConstraints.HORIZONTAL;
        gbc.gridx = 0;
        gbc.gridy = 1;
        gbc.weightx = 1.0;
        gbc.weighty = 0.0;
        gbc.gridwidth = 2;
        add(sequentView, gbc);

        if (sequentView instanceof InnerNodeView) {
            gbc.gridy = 2;
            add(((InnerNodeView) sequentView).tacletInfo, gbc);
        }

        gbc.fill = GridBagConstraints.BOTH;
        gbc.gridx = 0;
        gbc.gridy = 3;
        gbc.weighty = 1.0;
        add(javax.swing.Box.createGlue(), gbc);

        setBorder(new SequentHideWarningBorder(sequentView.getTitle(), sequentView));
        // setBorder(new TitledBorder("xxx"));

    }
}
