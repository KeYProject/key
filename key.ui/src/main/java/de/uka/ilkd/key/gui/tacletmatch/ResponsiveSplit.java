/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch;

import java.awt.*;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import javax.swing.*;

/**
 * Shows two components side by side in a horizontal split pane when there is enough width, and
 * collapses them into a tabbed pane when the available width drops below a threshold. Used to place
 * the taclet-match dialog's instantiation inputs next to the result preview, falling back to tabs
 * in
 * a narrow window.
 */
public class ResponsiveSplit extends JPanel {

    private static final long serialVersionUID = 1L;

    /** below this width the two sides are shown as tabs instead of a split */
    private static final int THRESHOLD = 720;

    private final JComponent left;
    private final String leftTitle;
    private final JComponent right;
    private final String rightTitle;

    /** current layout (null until first laid out): true = split, false = tabs */
    private Boolean wide;

    public ResponsiveSplit(JComponent left, String leftTitle, JComponent right, String rightTitle) {
        super(new BorderLayout());
        this.left = left;
        this.leftTitle = leftTitle;
        this.right = right;
        this.rightTitle = rightTitle;

        addComponentListener(new ComponentAdapter() {
            @Override
            public void componentResized(ComponentEvent e) {
                int w = getWidth();
                if (w >= 50) {
                    relayout(w >= THRESHOLD);
                }
            }
        });
        relayout(true);
    }

    private void relayout(boolean newWide) {
        if (wide != null && wide == newWide) {
            return;
        }
        wide = newWide;
        removeAll();
        if (newWide) {
            // let the divider travel the whole width: otherwise the scroll panes' minimum sizes
            // (driven by their content) pin it and it appears stuck
            left.setMinimumSize(new Dimension(0, 0));
            right.setMinimumSize(new Dimension(0, 0));
            // make the divider visible (FlatLaf renders it almost invisibly, and the divider itself
            // is a Container that does not paint a border): a line on each scroll pane's facing
            // edge
            // frames the grab strip
            Color line = UIManager.getColor("Separator.foreground");
            if (line == null) {
                line = UIManager.getColor("controlShadow");
            }
            if (line != null) {
                left.setBorder(BorderFactory.createMatteBorder(0, 0, 0, 1, line));
                right.setBorder(BorderFactory.createMatteBorder(0, 1, 0, 0, line));
            }
            JSplitPane split = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, left, right);
            split.setResizeWeight(0.6);
            split.setContinuousLayout(true);
            split.setDividerSize(8);
            split.setBorder(null);
            add(split, BorderLayout.CENTER);
        } else {
            left.setBorder(null);
            right.setBorder(null);
            JTabbedPane tabs = new JTabbedPane();
            tabs.addTab(leftTitle, left);
            tabs.addTab(rightTitle, right);
            add(tabs, BorderLayout.CENTER);
        }
        revalidate();
        repaint();
    }
}
