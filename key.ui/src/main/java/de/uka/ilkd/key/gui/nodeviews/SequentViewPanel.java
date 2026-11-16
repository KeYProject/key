/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import javax.swing.JPanel;

import org.jspecify.annotations.NullMarked;

/**
 * Creates the layout for SequentViews.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
@NullMarked
class SequentViewPanel extends JPanel {

    private static final long serialVersionUID = -4052156449188977483L;

    /**
     * Creates the layout for the given sequent view.
     *
     * <p>
     * The panel styles itself and wraps the sequent view while the receiver is still under
     * initialization (EISOP initialization check); the layout only materializes once the panel
     * is shown after construction, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
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

        if (sequentView instanceof InnerNodeView innerNodeView) {
            gbc.gridy = 2;
            add(((InnerNodeView) sequentView).getTacletInfo(), gbc);
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
