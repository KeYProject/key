/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch;

import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.VBox;

import de.uka.ilkd.key.gui.fx.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;

/**
 * Shared styling for the taclet-match dialog panels: titled sections, muted captions, a uniform
 * disclosure toggle and the monospaced text class. Sizes and spacing are only nudged for
 * readability; colours come from the shared theme CSS ({@code tacletmatch-*} classes in
 * {@code key-light.css} / {@code key-dark.css}).
 *
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.tacletmatch.TmStyle} (TmStyle.java:19-160). The Swing helper
 * reads the active look-and-feel's fonts and colours (UIManager); the FX version instead assigns
 * theme CSS classes and lets the stylesheet resolve the colours, so the dialog follows the light
 * and dark theme like the rest of the JavaFX UI. The {@code section} border becomes a titled
 * {@link VBox} (bold header with a hairline rule beneath it, no box); the footer skinning
 * (TmStyle.java:87-116) moves to the {@code tacletmatch-footer} CSS class, and the monospaced
 * {@code Font} to the {@link #MONO_CLASS} style class.
 */
public final class TmStyleF {

    /** style class rendering logic/term text monospaced (TmStyle.mono, TmStyle.java:29-33) */
    public static final String MONO_CLASS = "tacletmatch-mono";

    private TmStyleF() {}

    /** the muted caption label used for row labels and hints (TmStyle.muted) */
    public static Label muted(String text) {
        Label l = new Label(text);
        l.getStyleClass().add("tacletmatch-muted");
        return l;
    }

    /**
     * a titled section container with a bold header and inner spacing; further content is appended
     * by the caller (TmStyle.section, TmStyle.java:118-160: a bold section header with a hairline
     * rule beneath it and whitespace below — no box).
     */
    public static VBox section(String title) {
        VBox section = new VBox(4);
        section.getStyleClass().add("tacletmatch-section");
        section.getChildren().add(sectionTitle(title));
        return section;
    }

    /** like {@link #section(String)} with the section's content node already in place */
    public static VBox section(String title, Node content) {
        VBox section = section(title);
        section.getChildren().add(content);
        return section;
    }

    /**
     * a standalone bold section title (used by the classic dialog, which composes its own panels)
     */
    public static Node sectionTitle(String title) {
        Label l = new Label(title);
        l.getStyleClass().add("tacletmatch-section-title");
        return l;
    }

    /**
     * A small, unobtrusive disclosure (expand/collapse) toggle, used uniformly across the dialog so
     * every "show more" affordance looks and behaves the same. Collapsed shows {@code ▸}, expanded
     * {@code ▾}; update it with {@link #setDisclosure(Button, boolean)}
     * (TmStyle.disclosure, TmStyle.java:123-140).
     *
     * @param what what the toggle reveals, for the tooltip (e.g. "the full sequent"); {@code null}
     *        for a generic "Show more/less"
     */
    public static Button disclosure(String what) {
        Button b = new Button();
        b.setFocusTraversable(false);
        b.getStyleClass().add("tacletmatch-disclosure");
        b.getProperties().put("tm.what", what);
        setDisclosure(b, false);
        return b;
    }

    /**
     * updates the disclosure toggle's caret direction and tooltip for the expanded state
     * (TmStyle.setDisclosure, TmStyle.java:142-151).
     */
    public static void setDisclosure(Button b, boolean expanded) {
        b.setGraphic(IconFactoryF.createIcon(
            expanded ? FontAwesomeSolid.CARET_DOWN : FontAwesomeSolid.CARET_RIGHT, 12));
        Object what = b.getProperties().get("tm.what");
        if (what == null) {
            b.setTooltip(new Tooltip(expanded ? "Show less" : "Show more"));
        } else {
            b.setTooltip(new Tooltip((expanded ? "Hide " : "Show ") + what));
        }
    }
}
