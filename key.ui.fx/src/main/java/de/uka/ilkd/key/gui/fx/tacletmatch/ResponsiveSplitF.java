/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch;

import javafx.scene.Node;
import javafx.scene.control.SplitPane;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Region;

/**
 * Shows two components side by side in a horizontal split pane when there is enough width, and
 * collapses them into a tabbed pane when the available width drops below a threshold. Used to place
 * the taclet-match dialog's instantiation inputs next to the result preview, falling back to tabs
 * in a narrow window.
 *
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.tacletmatch.ResponsiveSplit} (ResponsiveSplit.java:19-93):
 * the Swing component-listener resize handling becomes a {@code widthProperty} listener with the
 * same {@link #THRESHOLD}; the {@code JSplitPane} with a 0.6 resize weight becomes a
 * {@link SplitPane} with an equivalent divider position.
 */
public class ResponsiveSplitF extends BorderPane {

    /** below this width the two sides are shown as tabs instead of a split */
    private static final int THRESHOLD = 720;

    private final Node left;
    private final String leftTitle;
    private final Node right;
    private final String rightTitle;

    /** current layout: true = split, false = tabs */
    private Boolean wide;

    public ResponsiveSplitF(Node left, String leftTitle, Node right, String rightTitle) {
        this.left = left;
        this.leftTitle = leftTitle;
        this.right = right;
        this.rightTitle = rightTitle;

        widthProperty().addListener((obs, oldW, newW) -> {
            if (newW.doubleValue() >= 50) {
                relayout(newW.doubleValue() >= THRESHOLD);
            }
        });
        relayout(true);
    }

    private void relayout(boolean newWide) {
        if (wide != null && wide == newWide) {
            return;
        }
        wide = newWide;
        if (newWide) {
            SplitPane split = new SplitPane(left, right);
            split.setDividerPosition(0, 0.6);
            // keep both sides from enforcing their content's minimum width (Swing set the scroll
            // panes' minimum size to 0 for the same reason)
            ((Region) left).setMinWidth(0);
            ((Region) right).setMinWidth(0);
            setCenter(split);
        } else {
            TabPane tabs = new TabPane(new Tab(leftTitle, left), new Tab(rightTitle, right));
            tabs.setTabClosingPolicy(TabPane.TabClosingPolicy.UNAVAILABLE);
            setCenter(tabs);
        }
    }
}
