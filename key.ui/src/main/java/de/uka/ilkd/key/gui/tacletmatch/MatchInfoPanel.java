/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch;

import java.awt.*;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import javax.swing.*;
import javax.swing.border.EmptyBorder;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;
import javax.swing.text.StyledDocument;

import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

/**
 * Overview of how the selected taclet matched the sequent: the schematic find pattern, the concrete
 * sub-term it was matched against, and the schema-variable bindings that the match determined.
 *
 * <p>
 * This makes explicit what the classic dialog left implicit. It is shown once per instantiation
 * alternative, since each alternative is a distinct match of the rule. Each bound schema variable
 * is
 * given a stable colour, used both for its binding chip and to highlight the sub-term it matched
 * inside the concrete matched term.
 */
public class MatchInfoPanel extends JPanel {

    private static final long serialVersionUID = 1L;

    /** label-column width so the value columns line up across the Rule/Find/Matched rows */
    private static final int LABEL_WIDTH = 92;

    /** a matched term taller than this many lines is collapsed behind a toggle */
    private static final int MATCHED_PREVIEW_LINES = 2;

    private final KeYMediator mediator;

    /**
     * stable palette index per bound schema variable, shared by the chips and the in-term highlight
     */
    private final Map<SchemaVariable, Integer> svColors = new LinkedHashMap<>();

    public MatchInfoPanel(TacletInstantiationModel model, KeYMediator mediator) {
        this.mediator = mediator;

        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));

        final TacletApp app = model.application();
        final Taclet taclet = app.taclet();
        final PosInOccurrence pio = app.posInOccurrence();
        final String side = pio == null ? null : (pio.isInAntec() ? "antecedent" : "succedent");

        int ci = 0;
        for (var entry : app.instantiations().getInstantiationMap()) {
            svColors.put(entry.key(), ci++);
        }

        setBorder(TmStyle.section(side == null ? "Match" : "Match — " + side));

        add(plainRow("Rule", taclet.name().toString()));

        if (taclet instanceof FindTaclet ft && pio != null) {
            add(monoRow("Find", TmPrint.term(mediator, ft.find())));
            add(matchedRow(ft.find(), pio.subTerm()));
        } else {
            add(plainRow("Find", "this rule has no find pattern"));
        }

        addBindings(app);

        // the full rule (incl. replacewith/add) is implementation detail: hidden behind a toggle
        addCollapsible("Rule body", TmPrint.taclet(mediator, taclet));
    }

    /**
     * a label row whose value is a disclosure toggle revealing the given (hidden) content below.
     */
    private void addCollapsible(String label, String content) {
        JPanel holder = new JPanel(new BorderLayout());
        holder.setOpaque(false);
        holder.setBorder(new EmptyBorder(2, LABEL_WIDTH, 2, 0));
        holder.add(new ExpandableText(content, Integer.MAX_VALUE), BorderLayout.CENTER);
        holder.setVisible(false);

        JButton disc = TmStyle.disclosure(label.toLowerCase());
        disc.addActionListener(e -> {
            boolean show = !holder.isVisible();
            holder.setVisible(show);
            TmStyle.setDisclosure(disc, show);
            revalidate();
            repaint();
        });

        JPanel toggleWrap = new JPanel(new FlowLayout(FlowLayout.LEFT, 0, 0));
        toggleWrap.setOpaque(false);
        toggleWrap.add(disc);
        add(row(label, toggleWrap));
        add(holder);
    }

    /**
     * lists the schema variables bound by the match, colour-coded, kept tight: {@code chip ↦ value}
     * with the arrow aligned across bindings so the variable stays next to its instantiation.
     */
    private void addBindings(TacletApp app) {
        var map = app.instantiations().getInstantiationMap();
        if (map.isEmpty()) {
            return;
        }
        List<JComponent> chips = new ArrayList<>();
        List<String> insts = new ArrayList<>();
        for (var entry : map) {
            chips.add(SvPalette.chip(entry.key().name().toString(),
                svColors.getOrDefault(entry.key(), 0)));
            insts.add(TmPrint.instantiation(mediator, entry.value()));
        }
        int chipWidth = 0;
        for (JComponent chip : chips) {
            chipWidth = Math.max(chipWidth, chip.getPreferredSize().width);
        }
        for (int i = 0; i < chips.size(); i++) {
            add(bindingRow(chips.get(i), insts.get(i), chipWidth));
        }
    }

    private JComponent bindingRow(JComponent chip, String inst, int chipWidth) {
        JPanel p = new JPanel(new BorderLayout(6, 0));
        p.setOpaque(false);
        // indent so the chip's left edge lands on the value column shared by the Find/Matched rows.
        // FlowLayout adds its hgap (6) before the first child too, so subtract it from the indent;
        // FlowLayout (unlike BoxLayout) keeps the chip and arrow vertically centred on one line.
        p.setBorder(new EmptyBorder(1, LABEL_WIDTH + 8 - 6, 1, 0));

        JPanel chipBox = new JPanel(new FlowLayout(FlowLayout.LEFT, 0, 0));
        chipBox.setOpaque(false);
        chipBox.add(chip);
        chipBox.setPreferredSize(new Dimension(chipWidth, chip.getPreferredSize().height));

        JPanel west = new JPanel(new FlowLayout(FlowLayout.LEFT, 6, 0));
        west.setOpaque(false);
        west.add(chipBox);
        west.add(new JLabel("↦"));

        p.add(west, BorderLayout.WEST);
        p.add(new ExpandableText(inst), BorderLayout.CENTER);
        return p;
    }

    private JComponent plainRow(String label, String value) {
        return row(label, leftLabel(new JLabel(value)));
    }

    private JComponent monoRow(String label, String value) {
        return row(label, new ExpandableText(value));
    }

    /**
     * the concrete matched term, set apart from the schematic find above and the bindings below by
     * a faint full-width band — clearly its own thing, but without a heavy box. Each bound schema
     * variable's sub-term is highlighted in the variable's colour, so the chips below read directly
     * off the term.
     */
    private JComponent matchedRow(Term find, Term matched) {
        JLabel l = new JLabel("Matched");
        l.setForeground(UIManager.getColor("Label.disabledForeground"));
        l.setPreferredSize(new Dimension(LABEL_WIDTH, l.getPreferredSize().height));

        JPanel band = new JPanel(new BorderLayout(8, 0));
        band.setOpaque(true);
        band.setBackground(TmStyle.tint());
        band.setBorder(new EmptyBorder(5, 0, 5, 0));
        band.add(l, BorderLayout.WEST);
        band.add(matchedTerm(find, matched), BorderLayout.CENTER);

        // an untinted gap above and below so the band floats between the find and the bindings
        JPanel wrap = new JPanel(new BorderLayout());
        wrap.setOpaque(false);
        wrap.setBorder(new EmptyBorder(4, 0, 4, 0));
        wrap.add(band, BorderLayout.CENTER);
        return wrap;
    }

    /**
     * a path inside the matched term together with the colour of the schema variable bound there
     */
    private record SvSpan(List<Integer> path, int color) {
    }

    /**
     * renders the matched term, colouring each sub-term a bound schema variable matched in its
     * variable's palette colour. A term taller than {@link #MATCHED_PREVIEW_LINES} lines is instead
     * shown collapsed behind a toggle via {@link ExpandableText} (the same component the bindings
     * use), so a big matched term does not dominate the panel; the in-term highlight is kept for
     * shorter terms, where the whole term is visible at once anyway. Falls back to plain text if
     * the
     * positions cannot be determined.
     */
    private JComponent matchedTerm(Term find, Term matched) {
        try {
            List<SvSpan> spans = new ArrayList<>();
            collectSvSpans(find, matched, new ArrayDeque<>(), spans);
            TmPrint.Positioned printed = TmPrint.termWithPositions(mediator, matched);
            if (printed.positions() == null || spans.isEmpty()
                    || TmText.lineCount(printed.text()) > MATCHED_PREVIEW_LINES) {
                return new ExpandableText(printed.text());
            }
            return styledTerm(printed.text(),
                resolveRanges(printed.text(), printed.positions(), spans));
        } catch (RuntimeException ex) {
            return new ExpandableText(TmPrint.term(mediator, matched));
        }
    }

    /**
     * walks the schematic find pattern and the concrete matched term in lock-step; wherever the
     * find
     * pattern is a (bound) schema variable, records the path so the matched sub-term there can be
     * highlighted.
     */
    private void collectSvSpans(Term find, Term matched, Deque<Integer> path, List<SvSpan> out) {
        if (find.op() instanceof SchemaVariable sv && svColors.containsKey(sv)) {
            out.add(new SvSpan(new ArrayList<>(path), svColors.get(sv)));
            return;
        }
        if (find.arity() != matched.arity()) {
            return;
        }
        for (int i = 0; i < find.arity(); i++) {
            path.addLast(i);
            collectSvSpans(find.sub(i), matched.sub(i), path, out);
            path.removeLast();
        }
    }

    /**
     * the sub-term ranges to highlight, resolved to character offsets {@code [start, end, colour]}.
     */
    private List<int[]> resolveRanges(String text, InitialPositionTable positions,
            List<SvSpan> spans) {
        List<int[]> ranges = new ArrayList<>();
        int len = text.length();
        for (SvSpan span : spans) {
            // the initial position table roots the printed term at path [0]; the sub-term path
            // follows below it
            ImmutableList<Integer> p = ImmutableList.singleton(0);
            for (int idx : span.path()) {
                p = p.append(idx);
            }
            Range r = positions.rangeForPath(p);
            if (r == null) {
                continue;
            }
            int start = Math.max(0, Math.min(r.start(), len));
            int end = Math.max(start, Math.min(r.end(), len));
            if (end > start) {
                ranges.add(new int[] { start, end, span.color() });
            }
        }
        return ranges;
    }

    /** a read-only monospaced pane showing {@code text} with the given coloured sub-term ranges. */
    private JTextPane styledTerm(String text, List<int[]> ranges) {
        JTextPane pane = new JTextPane();
        pane.setEditable(false);
        pane.setOpaque(false);
        pane.setBorder(null);
        pane.setText(text);

        StyledDocument doc = pane.getStyledDocument();
        Font mono = TmStyle.mono(pane);
        SimpleAttributeSet base = new SimpleAttributeSet();
        StyleConstants.setFontFamily(base, mono.getFamily());
        StyleConstants.setFontSize(base, mono.getSize());
        doc.setCharacterAttributes(0, text.length(), base, true);

        int len = text.length();
        for (int[] r : ranges) {
            int start = Math.min(r[0], len);
            int end = Math.min(r[1], len);
            if (end <= start) {
                continue;
            }
            SimpleAttributeSet a = new SimpleAttributeSet();
            StyleConstants.setBackground(a, SvPalette.background(r[2]));
            StyleConstants.setForeground(a, SvPalette.foreground(r[2]));
            doc.setCharacterAttributes(start, end - start, a, false);
        }
        // never stretch vertically beyond the content (BoxLayout would otherwise inflate it)
        pane.setMaximumSize(new Dimension(Integer.MAX_VALUE, pane.getPreferredSize().height));
        return pane;
    }

    /** a row whose label column holds an arbitrary component (e.g. a schema-variable chip). */
    private JComponent row(JComponent labelComp, JComponent value) {
        JPanel p = new JPanel(new BorderLayout(8, 0));
        p.setOpaque(false);
        p.setBorder(new EmptyBorder(1, 0, 1, 0));
        JPanel left = new JPanel(new FlowLayout(FlowLayout.LEFT, 0, 0));
        left.setOpaque(false);
        left.add(labelComp);
        left.setPreferredSize(new Dimension(LABEL_WIDTH, left.getPreferredSize().height));
        p.add(left, BorderLayout.WEST);
        p.add(value, BorderLayout.CENTER);
        return p;
    }

    private JComponent row(String label, JComponent value) {
        JPanel p = new JPanel(new BorderLayout(8, 0));
        p.setOpaque(false);
        p.setBorder(new EmptyBorder(1, 0, 1, 0));
        JLabel l = new JLabel(label);
        l.setForeground(UIManager.getColor("Label.disabledForeground"));
        Dimension d = l.getPreferredSize();
        l.setPreferredSize(new Dimension(LABEL_WIDTH, d.height));
        p.add(l, BorderLayout.WEST);
        p.add(value, BorderLayout.CENTER);
        return p;
    }

    /** left-aligns a component within a full-width, transparent container. */
    private static JComponent leftLabel(JComponent c) {
        c.setOpaque(false);
        return c;
    }
}
