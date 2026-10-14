/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration.fx;

import javafx.scene.paint.Color;

import de.uka.ilkd.key.gui.fx.colors.ColorSettingsF;
import de.uka.ilkd.key.gui.fx.prooftree.ProofTreeViewF;
import de.uka.ilkd.key.proof.Node;

import org.key_project.exploration.ExplorationNodeData;

/**
 * The proof-tree cell styler of the exploration extension, JavaFX port of the Swing {@code
 * ExplorationRenderer} (an inner {@code Styler} of ExplorationExtension.java:177-194, registered
 * into the proof tree renderer by {@code init}, ExplorationExtension.java:128): every node that
 * carries an {@link ExplorationNodeData} (an exploration action was performed on it or below it)
 * is rendered with a purple border and background and the "Exploration Action Performed"
 * tooltip title.
 * <p>
 * The FX counterpart implements the {@link ProofTreeViewF.CellStyler} hook (the Swing {@code
 * Styler} seam of the proof tree) and sets the border/background colors plus the tooltip title
 * on the {@link ProofTreeViewF.Style} the cells apply as their inline style.
 * <p>
 * The colors are the Swing defaults (dark {@code rgb(112, 17, 191)}, light {@code rgb(165, 146,
 * 191)}) behind the same {@code colors.json} keys {@code [proofTree]darkPurple}/
 * {@code [proofTree]lightPurple}, registered in the FX color registry {@link ColorSettingsF} —
 * user overrides and the shared colors file apply like in Swing.
 */
public final class ExplorationRendererF implements ProofTreeViewF.CellStyler {

    /** border color of explored branches (Swing {@code ExplorationRenderer.DARK_PURPLE_COLOR}). */
    public static final ColorSettingsF.ColorPropertyF DARK_PURPLE_COLOR =
        ColorSettingsF.define("[proofTree]darkPurple", "Border color of explored branches",
            Color.rgb(112, 17, 191));

    /** background color of explored branches (Swing {@code LIGHT_PURPLE_COLOR}). */
    public static final ColorSettingsF.ColorPropertyF LIGHT_PURPLE_COLOR =
        ColorSettingsF.define("[proofTree]lightPurple", "Background color of explored branches",
            Color.rgb(165, 146, 191));

    @Override
    public void style(ProofTreeViewF.Style style, ProofTreeViewF.Entry entry) {
        Node node = entry.node();
        ExplorationNodeData data = node.lookup(ExplorationNodeData.class);
        if (data != null) {
            style.setBorder(DARK_PURPLE_COLOR.getCurrentColor());
            style.setBackground(LIGHT_PURPLE_COLOR.getCurrentColor());
            style.setTooltipTitle("Exploration Action Performed");
        }
    }
}
