/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch;

import java.awt.*;
import javax.swing.*;

import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.executor.javadl.TacletExecutor;

import org.key_project.prover.sequent.FormulaChangeInfo;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

/**
 * Shows the sequent(s) that applying the taclet with the current instantiations would produce. The
 * result is computed with the executor's side-effect-free
 * {@link TacletExecutor#getResultSequentChanges} (never {@code Goal.apply}), so it does not touch
 * the proof. It refreshes, debounced, whenever the instantiations change; while they are incomplete
 * it shows a hint instead.
 */
public class ResultPreviewPanel extends JPanel {

    private static final long serialVersionUID = 1L;

    private final TacletInstantiationModel model;
    private final KeYMediator mediator;
    private final Goal goal;

    private final JPanel body = new JPanel();
    private Timer debounce;

    public ResultPreviewPanel(TacletInstantiationModel model, KeYMediator mediator, Goal goal) {
        this.model = model;
        this.mediator = mediator;
        this.goal = goal;

        setLayout(new BorderLayout());
        setBorder(TmStyle.section("Result preview"));
        body.setLayout(new BoxLayout(body, BoxLayout.Y_AXIS));
        // the resulting sequent sits on the editor (white in a light L&F) background to set it
        // apart
        // from the panel, while the section keeps its titled border
        body.setOpaque(true);
        Color editorBg = UIManager.getColor("TextArea.background");
        body.setBackground(editorBg != null ? editorBg : Color.WHITE);
        Color line = UIManager.getColor("Component.borderColor");
        body.setBorder(BorderFactory.createCompoundBorder(
            BorderFactory.createLineBorder(line != null ? line : Color.LIGHT_GRAY),
            BorderFactory.createEmptyBorder(8, 10, 8, 10)));
        add(body, BorderLayout.NORTH);

        update();
    }

    /** schedules a debounced refresh of the preview. */
    public void requestUpdate() {
        if (debounce == null) {
            debounce = new Timer(150, e -> update());
            debounce.setRepeats(false);
        }
        debounce.restart();
    }

    /** recomputes and renders the preview from the current instantiations. */
    public void update() {
        body.removeAll();
        try {
            TacletApp app = model.createTacletApp();
            if (app == null) {
                message("Could not apply the rule with the current instantiations.");
            } else {
                TacletExecutor exec = (TacletExecutor) app.taclet().getExecutor();
                ImmutableList<SequentChangeInfo> changes =
                    exec.getResultSequentChanges(goal, app);
                if (changes.isEmpty()) {
                    message("No preview available for this rule.");
                } else {
                    renderGoals(changes);
                }
            }
        } catch (Exception e) {
            message("Complete the instantiations to preview the result.");
        }
        body.revalidate();
        body.repaint();
    }

    private static final Color ADDED = new Color(0x1D9E75);
    private static final Color REMOVED = new Color(0xC0392B);

    private void renderGoals(ImmutableList<SequentChangeInfo> changes) {
        int n = changes.size();
        int i = 1;
        for (SequentChangeInfo sci : changes) {
            if (i > 1) {
                // a visible divider between resulting goals
                JPanel sep = new JPanel(new BorderLayout());
                sep.setOpaque(false);
                sep.setBorder(BorderFactory.createEmptyBorder(8, 0, 8, 0));
                sep.add(new JSeparator(), BorderLayout.CENTER);
                wrapInto(body, sep);
            }

            JPanel goal = new JPanel();
            goal.setLayout(new BoxLayout(goal, BoxLayout.Y_AXIS));
            goal.setOpaque(false);

            // the whole resulting sequent, hidden until the expand toggle is pressed
            ExpandableText full =
                new ExpandableText(printSequent(sci.sequent()), Integer.MAX_VALUE);
            full.setVisible(false);
            JButton toggle = expandToggle(full);

            int firstRow = goal.getComponentCount();
            if (n > 1) {
                // multiple goals: a header line carries the "Goal i of n" label and the toggle
                JPanel header = new JPanel(new BorderLayout());
                header.setOpaque(false);
                JLabel l = new JLabel("Goal " + i + " of " + n);
                l.setForeground(TmStyle.muted());
                header.add(l, BorderLayout.WEST);
                header.add(toggle, BorderLayout.EAST);
                wrapInto(goal, header);
                firstRow = goal.getComponentCount();
            }

            renderSide(goal, sci, true);
            renderSide(goal, sci, false);

            if (n == 1) {
                // single goal: no "Goal" label, so put the toggle on the first content row instead
                // of an empty line, so the sequent starts at the top of the card
                if (goal.getComponentCount() > firstRow
                        && goal.getComponent(firstRow) instanceof JPanel first) {
                    first.add(toggle, BorderLayout.EAST);
                } else {
                    JPanel header = new JPanel(new BorderLayout());
                    header.setOpaque(false);
                    header.add(toggle, BorderLayout.EAST);
                    wrapInto(goal, header);
                }
            }

            wrapInto(goal, full);
            wrapInto(body, goal);
            i++;
        }
    }

    /** a small, unobtrusive button that toggles the full-sequent view. */
    private JButton expandToggle(JComponent full) {
        JButton b = TmStyle.disclosure("the full sequent");
        b.addActionListener(e -> {
            boolean show = !full.isVisible();
            full.setVisible(show);
            TmStyle.setDisclosure(b, show);
            revalidate();
            repaint();
        });
        return b;
    }

    /** renders the added/removed/modified formulas of one side into the given container. */
    private void renderSide(JComponent container, SequentChangeInfo sci, boolean antec) {
        ImmutableList<SequentFormula> removed = sci.removedFormulas(antec);
        ImmutableList<SequentFormula> added = sci.addedFormulas(antec);
        ImmutableList<FormulaChangeInfo> modified = sci.modifiedFormulas(antec);
        if (removed.isEmpty() && added.isEmpty() && modified.isEmpty()) {
            return;
        }
        JLabel head = new JLabel(antec ? "antecedent" : "succedent");
        head.setForeground(TmStyle.muted());
        head.setBorder(BorderFactory.createEmptyBorder(4, 0, 1, 0));
        wrapInto(container, head);
        for (SequentFormula f : removed) {
            wrapInto(container, changeRow("−", REMOVED, f));
        }
        for (FormulaChangeInfo m : modified) {
            wrapInto(container, changeRow("−", REMOVED, m.getOriginalFormula()));
            wrapInto(container, changeRow("+", ADDED, m.newFormula()));
        }
        for (SequentFormula f : added) {
            wrapInto(container, changeRow("+", ADDED, f));
        }
    }

    private JComponent changeRow(String marker, Color color, SequentFormula f) {
        JPanel p = new JPanel(new BorderLayout(6, 0));
        p.setOpaque(false);
        JLabel m = new JLabel(marker);
        m.setForeground(color);
        m.setFont(m.getFont().deriveFont(Font.BOLD));
        m.setBorder(BorderFactory.createEmptyBorder(0, 8, 0, 0));
        p.add(m, BorderLayout.WEST);
        p.add(new ExpandableText(TmPrint.term(mediator, f.formula())), BorderLayout.CENTER);
        return p;
    }

    private void message(String text) {
        JLabel l = new JLabel(text);
        l.setForeground(TmStyle.muted());
        bodyAdd(l);
    }

    private void bodyAdd(JComponent c) {
        wrapInto(body, c);
    }

    /** adds a child wrapped so it fills the width (uniform alignment under a BoxLayout). */
    private static void wrapInto(JComponent container, JComponent c) {
        JPanel wrap = new JPanel(new BorderLayout());
        wrap.setOpaque(false);
        wrap.add(c, BorderLayout.CENTER);
        container.add(wrap);
    }

    private String printSequent(Sequent seq) {
        StringBuilder sb = new StringBuilder();
        for (SequentFormula sf : seq.antecedent()) {
            sb.append(TmPrint.term(mediator, sf.formula())).append('\n');
        }
        sb.append("⟹");
        for (SequentFormula sf : seq.succedent()) {
            sb.append('\n').append(TmPrint.term(mediator, sf.formula()));
        }
        return sb.toString();
    }
}
