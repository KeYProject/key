/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch;

import java.awt.*;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.List;
import javax.swing.*;
import javax.swing.border.EmptyBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.Highlighter;

import de.uka.ilkd.key.control.instantiation_model.TacletAssumesModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.io.ProofSaver;

import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.parsing.Position;

/**
 * Lets the user instantiate the taclet's {@code \assumes} sequent in one of two ways, chosen with a
 * toggle:
 * <ul>
 * <li><b>Select from sequent</b> &ndash; per assumes formula, pick a matching sequent formula from
 * a
 * list (sequent-view-like);</li>
 * <li><b>Type the {@code \assumes} sequent</b> &ndash; type the whole instantiated assumes sequent
 * (antecedent {@code ==>} succedent). It is checked incrementally: parse/syntax of the sequent, the
 * expected number of formulas, and &ndash; via the dialog status &ndash; whether it is compatible
 * with the existing schema-variable bindings.</li>
 * </ul>
 */
public class AssumesSelectionPanel extends JPanel {

    private static final long serialVersionUID = 1L;

    /** abbreviate candidate text longer than this in the list (full text on hover) */
    private static final int ABBREV_LIMIT = 200;

    private static final Color OK_COLOR = new Color(0x1D9E75);
    private static final Color WARN_COLOR = new Color(0xBA7517);
    private static final Color ERROR_COLOR = new Color(0xC0392B);

    private static final Highlighter.HighlightPainter ERROR_PAINTER =
        new DefaultHighlighter.DefaultHighlightPainter(new Color(0xF7C1C1));

    private final TacletInstantiationModel model;
    private final KeYMediator mediator;
    private final Services services;
    private final Runnable onChange;

    private final int anteSize;
    private final int count;

    /** per-formula combo models (index 0..anteSize-1 antecedent, rest succedent) */
    private final TacletAssumesModel[] choices;
    /** the "Manual Input" sentinel of each combo model */
    private final AssumesFormulaInstantiation[] sentinels;
    /** the candidate lists, one per assumes formula (select mode) */
    private final List<JList<AssumesFormulaInstantiation>> lists = new ArrayList<>();

    private final CardLayout cards = new CardLayout();
    private final JPanel cardPanel = new JPanel(cards);
    private final JTextArea anteArea = new JTextArea(4, 28);
    private final JTextArea succArea = new JTextArea(4, 28);
    private final JLabel manualStatus = new JLabel(" ");

    private boolean manualMode;

    public AssumesSelectionPanel(TacletInstantiationModel model, KeYMediator mediator,
            Runnable onChange) {
        this.model = model;
        this.mediator = mediator;
        this.services = mediator.getServices();
        this.onChange = onChange;

        Sequent assumes = model.application().taclet().assumesSequent();
        this.anteSize = assumes.antecedent().size();
        this.count = model.ifChoiceModelCount();

        this.choices = new TacletAssumesModel[count];
        this.sentinels = new AssumesFormulaInstantiation[count];
        for (int i = 0; i < count; i++) {
            choices[i] = model.ifChoiceModel(i);
            sentinels[i] = choices[i].getElementAt(choices[i].getSize() - 1);
        }

        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
        setBorder(TmStyle.section("Assumptions (\\assumes)"));

        add(buildToggle());
        cardPanel.add(buildSelectCard(), "select");
        cardPanel.add(buildManualCard(), "manual");
        cardPanel.setAlignmentX(LEFT_ALIGNMENT);
        add(cardPanel);

        showSelect();
    }

    private JComponent buildToggle() {
        JRadioButton selectBtn = new JRadioButton("Select from sequent", true);
        JRadioButton manualBtn = new JRadioButton("Type the \\assumes sequent");
        ButtonGroup group = new ButtonGroup();
        group.add(selectBtn);
        group.add(manualBtn);
        selectBtn.addActionListener(e -> showSelect());
        manualBtn.addActionListener(e -> showManual());

        JPanel row = new JPanel(new FlowLayout(FlowLayout.LEFT, 8, 0));
        row.setOpaque(false);
        row.setAlignmentX(LEFT_ALIGNMENT);
        row.add(selectBtn);
        row.add(manualBtn);
        return row;
    }

    private JComponent buildSelectCard() {
        JPanel card = new JPanel();
        card.setLayout(new BoxLayout(card, BoxLayout.Y_AXIS));
        card.setOpaque(false);

        for (int i = 0; i < count; i++) {
            card.add(buildFormulaSelector(i));
        }
        return card;
    }

    private JComponent buildFormulaSelector(int index) {
        JPanel p = new JPanel();
        p.setLayout(new BoxLayout(p, BoxLayout.Y_AXIS));
        p.setOpaque(false);
        p.setAlignmentX(LEFT_ALIGNMENT);
        p.setBorder(new EmptyBorder(4, 0, 8, 0));

        JPanel header = new JPanel(new FlowLayout(FlowLayout.LEFT, 6, 0));
        header.setOpaque(false);
        header.setAlignmentX(LEFT_ALIGNMENT);
        JLabel lbl = new JLabel((index < anteSize ? "antecedent" : "succedent") + ":");
        lbl.setForeground(UIManager.getColor("Label.disabledForeground"));
        header.add(lbl);
        header.add(new ExpandableText(ProofSaver.printAnything(model.ifFma(index), services)));
        p.add(header);

        DefaultListModel<AssumesFormulaInstantiation> lm = new DefaultListModel<>();
        for (int k = 0; k < choices[index].getSize() - 1; k++) {
            lm.addElement(choices[index].getElementAt(k));
        }
        JList<AssumesFormulaInstantiation> list = new JList<>(lm) {
            @Override
            public String getToolTipText(MouseEvent e) {
                int idx = locationToIndex(e.getPoint());
                return idx >= 0 ? TmText.htmlTooltip(text(getModel().getElementAt(idx))) : null;
            }
        };
        list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        list.setVisibleRowCount(Math.min(Math.max(lm.getSize(), 1), 4));
        list.setCellRenderer(new CandidateRenderer());
        list.addListSelectionListener(e -> {
            if (!e.getValueIsAdjusting() && !manualMode && list.getSelectedValue() != null) {
                choices[index].setSelectedItem(list.getSelectedValue());
                onChange.run();
            }
        });
        lists.add(list);

        if (lm.isEmpty()) {
            JLabel none = new JLabel("(no matching formula — use \"Type the \\assumes sequent\")");
            none.setForeground(UIManager.getColor("Label.disabledForeground"));
            none.setAlignmentX(LEFT_ALIGNMENT);
            p.add(none);
        } else {
            JScrollPane sp = new JScrollPane(list);
            sp.setAlignmentX(LEFT_ALIGNMENT);
            p.add(sp);
            list.setSelectedIndex(selectedIndexOf(index, lm));
        }
        return p;
    }

    private int selectedIndexOf(int index, DefaultListModel<AssumesFormulaInstantiation> lm) {
        Object selected = choices[index].getSelectedItem();
        for (int k = 0; k < lm.getSize(); k++) {
            if (lm.getElementAt(k) == selected) {
                return k;
            }
        }
        return 0;
    }

    private JComponent buildManualCard() {
        JPanel card = new JPanel();
        card.setLayout(new BoxLayout(card, BoxLayout.Y_AXIS));
        card.setOpaque(false);

        JPanel guide = new JPanel(new BorderLayout(6, 0));
        guide.setOpaque(false);
        guide.setAlignmentX(LEFT_ALIGNMENT);
        JLabel gl = new JLabel("schematic");
        gl.setForeground(UIManager.getColor("Label.disabledForeground"));
        guide.add(gl, BorderLayout.WEST);
        guide.add(new ExpandableText(schematicSequent()), BorderLayout.CENTER);
        card.add(guide);

        JPanel editor = new JPanel();
        editor.setLayout(new BoxLayout(editor, BoxLayout.X_AXIS));
        editor.setOpaque(false);
        editor.setAlignmentX(LEFT_ALIGNMENT);
        editor.setBorder(new EmptyBorder(6, 0, 4, 0));
        editor.add(labeledArea("antecedent", anteArea));
        JLabel arrow = new JLabel("  ⟹  ");
        editor.add(arrow);
        editor.add(labeledArea("succedent", succArea));
        card.add(editor);

        DocumentListener dl = new DocumentListener() {
            @Override
            public void insertUpdate(DocumentEvent e) {
                scheduleValidation();
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                scheduleValidation();
            }

            @Override
            public void changedUpdate(DocumentEvent e) {
                scheduleValidation();
            }
        };
        anteArea.getDocument().addDocumentListener(dl);
        succArea.getDocument().addDocumentListener(dl);

        manualStatus.setAlignmentX(LEFT_ALIGNMENT);
        card.add(manualStatus);
        return card;
    }

    private JComponent labeledArea(String label, JTextArea area) {
        area.setFont(TmStyle.mono(area));
        area.setLineWrap(true);
        area.setWrapStyleWord(true);
        JPanel p = new JPanel(new BorderLayout(0, 2));
        p.setOpaque(false);
        JLabel l = new JLabel(label);
        l.setForeground(UIManager.getColor("Label.disabledForeground"));
        p.add(l, BorderLayout.NORTH);
        p.add(new JScrollPane(area), BorderLayout.CENTER);
        return p;
    }

    private Timer debounce;

    private void scheduleValidation() {
        if (!manualMode) {
            return;
        }
        if (debounce == null) {
            debounce = new Timer(300, e -> validateManual());
            debounce.setRepeats(false);
        }
        debounce.restart();
    }

    private void showSelect() {
        manualMode = false;
        cards.show(cardPanel, "select");
        for (int i = 0; i < count; i++) {
            AssumesFormulaInstantiation v =
                i < lists.size() ? lists.get(i).getSelectedValue() : null;
            if (v != null) {
                choices[i].setSelectedItem(v);
            }
            model.setManualInput(i, "");
        }
        onChange.run();
    }

    private void showManual() {
        manualMode = true;
        cards.show(cardPanel, "manual");
        validateManual();
    }

    /**
     * parses and checks the typed assumes sequent, then feeds it to the per-formula models so the
     * dialog status reflects compatibility with the existing bindings.
     */
    private void validateManual() {
        clearErrorHighlights();
        String ante = anteArea.getText();
        String succ = succArea.getText();
        if (ante.isBlank() && succ.isBlank()) {
            status(WARN_COLOR, "● waiting for the \\assumes sequent…");
            clearManual();
            onChange.run();
            return;
        }

        Sequent parsed;
        try {
            parsed = new KeyIO(services).parseSequent(AssumesInput.combined(ante, succ));
        } catch (Exception e) {
            reportSyntaxError(e);
            clearManual();
            onChange.run();
            return;
        }

        String arity = AssumesInput.arityError(parsed.antecedent().size(),
            parsed.succedent().size(), anteSize, count - anteSize);
        if (arity != null) {
            status(ERROR_COLOR, "✗ " + arity);
            clearManual();
            onChange.run();
            return;
        }

        int i = 0;
        for (SequentFormula sf : parsed.antecedent()) {
            applyManual(i++, sf);
        }
        for (SequentFormula sf : parsed.succedent()) {
            applyManual(i++, sf);
        }

        // compatibility with the existing bindings is reflected by the model status
        AssumesInput.ModelStatus st = AssumesInput.classify(model.getStatusString());
        if (st.kind() == AssumesInput.StatusKind.OK) {
            status(OK_COLOR, "✓ " + st.text());
        } else {
            status(WARN_COLOR, "● " + st.text());
        }
        onChange.run();
    }

    private void applyManual(int index, SequentFormula sf) {
        choices[index].setSelectedItem(sentinels[index]);
        model.setManualInput(index, ProofSaver.printAnything(sf.formula(), services));
    }

    private void clearManual() {
        // keep the model in "manual" selection so an empty/invalid editor reads as incomplete
        // rather than silently falling back to the select-mode candidate
        for (int i = 0; i < count; i++) {
            choices[i].setSelectedItem(sentinels[i]);
            model.setManualInput(i, "");
        }
    }

    /** writes the current input back to the model (selections are applied live). */
    public void pushAllInputToModel() {
        if (manualMode) {
            validateManual();
        } else {
            showSelect();
        }
    }

    private void status(Color color, String text) {
        manualStatus.setForeground(color);
        manualStatus.setText(text);
    }

    /**
     * reports a parse failure: a clean message (without the noisy " at &lt;pos&gt;"/"unknown") and,
     * if the failure carries a location, a highlight at the offending position in the editor.
     */
    private void reportSyntaxError(Throwable e) {
        AssumesInput.SyntaxError err = AssumesInput.extract(e);
        status(ERROR_COLOR, "✗ " + err.message());

        Position pos = err.position();
        if (pos != null) {
            String combined = AssumesInput.combined(anteArea.getText(), succArea.getText());
            int off = TmText.offsetOf(combined, pos.line(), pos.column());
            AssumesInput.Target target = AssumesInput.locate(anteArea.getText(), off);
            // a position inside the synthetic "==>" separator belongs to neither editor
            if (target.side() == AssumesInput.Side.ANTECEDENT) {
                highlightAt(anteArea, target.offset());
            } else if (target.side() == AssumesInput.Side.SUCCEDENT) {
                highlightAt(succArea, target.offset());
            }
        }
    }

    private static void highlightAt(JTextArea area, int offset) {
        int len = area.getDocument().getLength();
        int start = Math.max(0, Math.min(offset, len));
        int end = Math.min(start + 1, len);
        if (start == end && start > 0) {
            start = end - 1;
        }
        try {
            area.getHighlighter().addHighlight(start, Math.max(end, start), ERROR_PAINTER);
            area.setCaretPosition(start);
        } catch (BadLocationException ignored) {
            // position out of range; nothing to highlight
        }
    }

    private void clearErrorHighlights() {
        anteArea.getHighlighter().removeAllHighlights();
        succArea.getHighlighter().removeAllHighlights();
    }

    private String schematicSequent() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < anteSize; i++) {
            if (i > 0) {
                sb.append(", ");
            }
            sb.append(TmPrint.term(mediator, model.ifFma(i)));
        }
        sb.append("  ==>  ");
        for (int i = anteSize; i < count; i++) {
            if (i > anteSize) {
                sb.append(", ");
            }
            sb.append(TmPrint.term(mediator, model.ifFma(i)));
        }
        return sb.toString();
    }

    private String text(AssumesFormulaInstantiation inst) {
        SequentFormula sf = inst.getSequentFormula();
        return sf != null ? TmPrint.term(mediator, sf.formula()) : inst.toString();
    }

    private final class CandidateRenderer extends DefaultListCellRenderer {
        private static final long serialVersionUID = 1L;

        @Override
        public Component getListCellRendererComponent(JList<?> l, Object value, int index,
                boolean isSelected, boolean cellHasFocus) {
            JLabel c = (JLabel) super.getListCellRendererComponent(l, value, index, isSelected,
                cellHasFocus);
            // flatten a possibly multi-line, wrapped formula to one line so the whole thing shows
            // (up to the abbreviation limit) instead of just its first wrapped segment
            c.setText(TmText.collapseToLine(text((AssumesFormulaInstantiation) value),
                ABBREV_LIMIT));
            c.setFont(TmStyle.mono(c));
            return c;
        }
    }
}
