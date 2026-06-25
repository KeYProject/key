/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch;

import java.awt.*;
import javax.swing.*;

/**
 * Read-only monospaced text that abbreviates long or multi-line content to a single truncated line
 * and offers a toggle to expand it to its full, wrapped form. The full text is also available as a
 * tooltip. Used for the (potentially very long) terms and formulas shown across the taclet-match
 * dialog so they neither blow up the layout nor hide information.
 */
public class ExpandableText extends JPanel {

    private static final long serialVersionUID = 1L;

    /** collapse content longer than this many characters */
    private static final int DEFAULT_LIMIT = 240;

    private final String full;
    private final int limit;
    private final boolean expandable;
    private boolean expanded;

    private final JTextArea area = new JTextArea();
    private final JButton toggle = TmStyle.disclosure(null);

    public ExpandableText(String text) {
        this(text, DEFAULT_LIMIT);
    }

    public ExpandableText(String text, int limit) {
        this.full = text == null ? "" : text;
        this.limit = limit;
        // collapse genuinely long content, or anything taller than two lines, so a big term does
        // not dominate the panel; short one/two-line terms are shown in full (wrapped)
        this.expandable = full.length() > limit || TmText.lineCount(full) > 2;

        setOpaque(false);
        setLayout(new BorderLayout(4, 0));

        area.setEditable(false);
        area.setOpaque(false);
        // read-only display: don't take focus (avoids a blinking caret and keeps the tab order on
        // the editable instantiation fields)
        area.setFocusable(false);
        area.setFont(TmStyle.mono(area));
        area.setToolTipText(TmText.htmlTooltip(full));
        add(area, BorderLayout.CENTER);

        if (expandable) {
            toggle.addActionListener(e -> {
                expanded = !expanded;
                updateView();
            });
            JPanel east = new JPanel(new BorderLayout());
            east.setOpaque(false);
            east.add(toggle, BorderLayout.NORTH);
            add(east, BorderLayout.EAST);
        }
        updateView();
    }

    @Override
    public Dimension getMaximumSize() {
        // fill horizontally but never stretch vertically beyond the content (BoxLayout otherwise
        // inflates JTextArea-based components to absorb slack)
        return new Dimension(Integer.MAX_VALUE, getPreferredSize().height);
    }

    private void updateView() {
        if (!expandable) {
            area.setLineWrap(true);
            area.setWrapStyleWord(true);
            area.setText(full);
            return;
        }
        if (expanded) {
            area.setLineWrap(true);
            area.setWrapStyleWord(true);
            area.setText(full);
        } else {
            area.setLineWrap(false);
            area.setText(TmText.collapseToLine(full, limit));
        }
        TmStyle.setDisclosure(toggle, expanded);
        revalidate();
    }
}
