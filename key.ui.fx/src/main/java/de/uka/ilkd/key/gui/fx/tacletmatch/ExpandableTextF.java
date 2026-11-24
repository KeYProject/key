/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch;

import javafx.geometry.Pos;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.text.Font;

/**
 * Read-only monospaced text that abbreviates long or multi-line content to a single truncated line
 * and offers a toggle to expand it to its full, wrapped form. The full text is also available as a
 * tooltip. Used for the (potentially very long) terms and formulas shown across the taclet-match
 * dialog so they neither blow up the layout nor hide information.
 *
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.tacletmatch.ExpandableText} (ExpandableText.java:16-92): the
 * Swing version was a read-only {@code JTextArea} plus a {@code TmStyle.disclosure} button; the FX
 * version is an {@link HBox} with a wrapping {@link Label} plus the disclosure toggle.
 */
public class ExpandableTextF extends HBox {

    /** collapse content longer than this many characters (ExpandableText.java:21) */
    private static final int DEFAULT_LIMIT = 240;

    /**
     * a monospaced font for logic/term text, slightly larger than the default
     * (TmStyle.mono, TmStyle.java:29-33) — used where a plain (styled) control must render logic
     * text without carrying the {@link TmStyleF#MONO_CLASS} stylesheet class.
     */
    public static Font mono() {
        return Font.font("monospaced", 12 + FONT_BUMP);
    }

    /** logic/term text is rendered a couple of points larger than the default for legibility */
    private static final int FONT_BUMP = 2;

    private final String full;
    private final int limit;
    private final boolean expandable;
    private boolean expanded;

    private final Label area = new Label();
    private final Button toggle = TmStyleF.disclosure(null);

    public ExpandableTextF(String text) {
        this(text, DEFAULT_LIMIT);
    }

    public ExpandableTextF(String text, int limit) {
        this.full = text == null ? "" : text;
        this.limit = limit;
        // collapse genuinely long content, or anything taller than two lines, so a big term does
        // not dominate the panel; short one/two-line terms are shown in full (wrapped)
        this.expandable = full.length() > limit || TmTextF.lineCount(full) > 2;

        getStyleClass().add("tacletmatch-expandable");
        setSpacing(4);
        setAlignment(Pos.CENTER_LEFT);

        area.getStyleClass().add(TmStyleF.MONO_CLASS);
        area.setWrapText(true);
        area.setTooltip(new Tooltip(full));
        HBox.setHgrow(area, Priority.ALWAYS);
        getChildren().add(area);

        if (expandable) {
            toggle.setOnAction(e -> {
                expanded = !expanded;
                updateView();
            });
            getChildren().add(toggle);
        }
        updateView();
    }

    private void updateView() {
        if (!expandable || expanded) {
            area.setWrapText(true);
            area.setText(full);
        } else {
            area.setWrapText(false);
            area.setText(TmTextF.collapseToLine(full, limit));
        }
        TmStyleF.setDisclosure(toggle, expanded);
    }

    /** the full, untruncated text this node displays when expanded */
    public String getFullText() {
        return full;
    }

    /** whether the content is collapsed to the abbreviated line */
    public boolean isExpanded() {
        return expanded;
    }

    /** {@inheritDoc} fill horizontally but never grow vertically beyond the content */
    @Override
    protected double computeMaxHeight(double width) {
        return super.computePrefHeight(width);
    }

}
