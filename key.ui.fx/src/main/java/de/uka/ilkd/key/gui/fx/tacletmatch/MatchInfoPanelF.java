/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.layout.VBox;

import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.fxmisc.richtext.InlineCssTextArea;

/**
 * Overview of how the selected taclet matched the sequent: the schematic find pattern, the concrete
 * sub-term it was matched against, and the schema-variable bindings that the match determined.
 *
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.tacletmatch.MatchInfoPanel} (MatchInfoPanel.java:44-344). This
 * makes explicit what the classic dialog left implicit. It is shown once per instantiation
 * alternative, since each alternative is a distinct match of the rule. Each bound schema variable
 * is given a stable colour, used both for its binding chip and to highlight the sub-term it matched
 * inside the concrete matched term — the match highlighting view of the redesigned dialog. The
 * matched term is rendered with a read-only RichTextFX area (the counter-part of the Swing
 * read-only {@code JTextPane} with character attributes, MatchInfoPanel.java:281-310): each
 * schema-variable span carries the variable's chip colour as a text background.
 */
public class MatchInfoPanelF extends VBox {

    /** label-column width so the value columns line up across the Rule/Find/Matched rows */
    private static final int LABEL_WIDTH = 92;

    /** a matched term taller than this many lines is collapsed behind a toggle */
    private static final int MATCHED_PREVIEW_LINES = 2;

    /** inline CSS giving the highlight spans their background colour (RichTextFX per-span style) */
    private static final String HIGHLIGHT_CSS = "-rtfx-background-color: ";

    /**
     * stable palette index per bound schema variable, shared by the chips and the in-term
     * highlight
     */
    private final Map<SchemaVariable, Integer> svColors = new LinkedHashMap<>();

    /** the number of schema-variable spans actually highlighted inside the matched term */
    private int highlightSpanCount;

    private final Services services;
    private final NotationInfo notationInfo;

    /** the titled section box holding the rows */
    private final VBox body;

    public MatchInfoPanelF(TacletInstantiationModel model, Services services,
            NotationInfo notationInfo) {
        this.services = services;
        this.notationInfo = notationInfo;

        setSpacing(3);

        final TacletApp app = model.application();
        final Taclet taclet = app.taclet();
        final PosInOccurrence pio = app.posInOccurrence();
        final String side = pio == null ? null : (pio.isInAntec() ? "antecedent" : "succedent");

        int ci = 0;
        for (var entry : app.instantiations().getInstantiationMap()) {
            svColors.put(entry.key(), ci++);
        }

        // the panel is the titled section (title, hairline rule, content)
        VBox section = TmStyleF.section(side == null ? "Match" : "Match — " + side);
        this.body = section;
        getChildren().add(section);

        add(plainRow("Rule", taclet.name().toString()));

        if (taclet instanceof FindTaclet ft && pio != null) {
            add(monoRow("Find", TmPrintF.term(services, notationInfo, ft.find())));
            add(matchedRow(ft.find(), pio.subTerm()));
        } else {
            add(plainRow("Find", "this rule has no find pattern"));
        }

        addBindings(app);

        // the full rule (incl. replacewith/add) is implementation detail: hidden behind a toggle
        addCollapsible("Rule body", TmPrintF.taclet(services, notationInfo, taclet));
    }

    /**
     * @return how many schema-variable sub-terms are currently highlighted inside the matched term
     *         (used by the self test to assert the match highlighting renders)
     */
    public int getHighlightSpanCount() {
        return highlightSpanCount;
    }

    /**
     * a standalone bold section title (used by the classic dialog, which composes its own panels
     * from the shared helpers)
     */
    public static Node sectionTitle(String title) {
        return TmStyleF.sectionTitle(title);
    }

    private void add(Node n) {
        body.getChildren().add(n);
    }

    /**
     * a label row whose value is a disclosure toggle revealing the given (hidden) content below
     * (MatchInfoPanel.java:96-117).
     */
    private void addCollapsible(String label, String content) {
        VBox holder = new VBox();
        holder.getStyleClass().add("tacletmatch-muted");
        holder.getChildren().add(new ExpandableTextF(content, Integer.MAX_VALUE));
        holder.setVisible(false);
        holder.setManaged(false);

        Button disc = TmStyleF.disclosure(label.toLowerCase());
        disc.setOnAction(e -> {
            boolean show = !holder.isVisible();
            holder.setVisible(show);
            holder.setManaged(show);
            TmStyleF.setDisclosure(disc, show);
        });

        add(row(label, disc));
        add(holder);
    }

    /**
     * lists the schema variables bound by the match, colour-coded, kept tight: {@code chip ↦ value}
     * with the arrow aligned across bindings (MatchInfoPanel.java:123-165).
     */
    private void addBindings(TacletApp app) {
        var map = app.instantiations().getInstantiationMap();
        if (map.isEmpty()) {
            return;
        }
        List<Label> chips = new ArrayList<>();
        List<String> insts = new ArrayList<>();
        for (var entry : map) {
            chips.add(SvPaletteF.chip(entry.key().name().toString(),
                svColors.getOrDefault(entry.key(), 0)));
            insts.add(TmPrintF.instantiation(services, notationInfo, entry.value()));
        }
        for (int i = 0; i < chips.size(); i++) {
            add(bindingRow(chips.get(i), insts.get(i)));
        }
    }

    private Node bindingRow(Label chip, String inst) {
        HBox p = new HBox(6);
        p.getStyleClass().add("tacletmatch-row");
        // indent so the chip's left edge lands on the value column shared by the Find/Matched rows
        p.setPadding(new javafx.geometry.Insets(1, 0, 1, LABEL_WIDTH + 8));

        HBox chipBox = new HBox(chip);
        chipBox.setAlignment(Pos.CENTER_LEFT);

        Label arrow = new Label("↦");

        ExpandableTextF value = new ExpandableTextF(inst);
        HBox.setHgrow(value, Priority.ALWAYS);

        p.getChildren().addAll(chipBox, arrow, value);
        return p;
    }

    private Node plainRow(String label, String value) {
        Label l = new Label(value);
        l.setWrapText(true);
        return row(label, l);
    }

    private Node monoRow(String label, String value) {
        return row(label, new ExpandableTextF(value));
    }

    /**
     * the concrete matched term, set apart from the schematic find above and the bindings below by
     * a faint full-width band — clearly its own thing, but without a heavy box
     * (MatchInfoPanel.java:181-199).
     */
    private Node matchedRow(Term find, Term matched) {
        Label l = TmStyleF.muted("Matched");

        HBox band = new HBox(8);
        band.getStyleClass().add("tacletmatch-matched-band");
        band.setAlignment(Pos.CENTER_LEFT);
        band.getChildren().addAll(l, matchedTerm(find, matched));

        // an untinted gap above and below so the band floats between the find and the bindings
        HBox wrap = new HBox(band);
        wrap.setPadding(new javafx.geometry.Insets(4, 0, 4, 0));
        return wrap;
    }

    /**
     * a path inside the matched term together with the colour of the schema variable bound there
     * (MatchInfoPanel.java:203-205).
     */
    private record SvSpan(List<Integer> path, int color) {
    }

    /**
     * renders the matched term, colouring each sub-term a bound schema variable matched in its
     * variable's palette colour. A term taller than {@link #MATCHED_PREVIEW_LINES} lines is instead
     * shown collapsed behind a toggle via {@link ExpandableTextF} (the same component the bindings
     * use), so a big matched term does not dominate the panel; the in-term highlight is kept for
     * shorter terms, where the whole term is visible at once anyway. Falls back to plain text if
     * the positions cannot be determined (MatchInfoPanel.java:216-230).
     */
    private Node matchedTerm(Term find, Term matched) {
        try {
            List<SvSpan> spans = new ArrayList<>();
            collectSvSpans(find, matched, new ArrayDeque<>(), spans);
            TmPrintF.Positioned printed =
                TmPrintF.termWithPositions(services, notationInfo, matched);
            if (printed.positions() == null || spans.isEmpty()
                    || TmTextF.lineCount(printed.text()) > MATCHED_PREVIEW_LINES) {
                highlightSpanCount = 0;
                return new ExpandableTextF(printed.text());
            }
            return styledTerm(printed.text(), resolveRanges(printed.text(), printed.positions(),
                spans));
        } catch (RuntimeException ex) {
            highlightSpanCount = 0;
            return new ExpandableTextF(TmPrintF.term(services, notationInfo, matched));
        }
    }

    /**
     * walks the schematic find pattern and the concrete matched term in lock-step; wherever the
     * find pattern is a (bound) schema variable, records the path so the matched sub-term there can
     * be highlighted (MatchInfoPanel.java:238-251).
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
     * the sub-term ranges to highlight, resolved to character offsets {@code [start, end, colour]}
     * (MatchInfoPanel.java:256-278).
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

    /**
     * a read-only monospaced area showing {@code text} with the given coloured sub-term ranges —
     * the FX counter-part of the Swing {@code styledTerm} JTextPane (MatchInfoPanel.java:280-310):
     * the character-attribute backgrounds become RichTextFX per-span background styles.
     */
    private Node styledTerm(String text, List<int[]> ranges) {
        InlineCssTextArea area = new InlineCssTextArea(text);
        area.setEditable(false);
        area.setFocusTraversable(false);
        area.setWrapText(true);
        area.getStyleClass().add(TmStyleF.MONO_CLASS);
        area.setStyle(0, text.length(), "-rtfx-background-color: transparent;");

        int len = text.length();
        for (int[] r : ranges) {
            int start = Math.min(r[0], len);
            int end = Math.min(r[1], len);
            if (end <= start) {
                continue;
            }
            area.setStyle(start, end,
                HIGHLIGHT_CSS + SvPaletteF.backgroundCss(r[2]) + ";");
            highlightSpanCount++;
        }

        // never stretch vertically beyond the content (the surrounding column would inflate it)
        double lineEstimate = 24;
        int rows = Math.min(TmTextF.lineCount(text), 3);
        area.setPrefHeight(rows * lineEstimate + 4);
        area.setMaxHeight(Region.USE_PREF_SIZE);
        area.setPadding(new javafx.geometry.Insets(1, 2, 1, 2));
        HBox.setHgrow(area, Priority.ALWAYS);
        return area;
    }

    /** a row whose label column holds an arbitrary component (e.g. a schema-variable chip) */
    private Node row(String label, Node value) {
        Label l = TmStyleF.muted(label);
        l.setMinWidth(LABEL_WIDTH);
        l.setMaxWidth(LABEL_WIDTH);
        HBox p = new HBox(8);
        p.getStyleClass().add("tacletmatch-row");
        p.setAlignment(Pos.TOP_LEFT);
        p.getChildren().addAll(l, value);
        HBox.setHgrow(value, Priority.ALWAYS);
        return p;
    }
}
