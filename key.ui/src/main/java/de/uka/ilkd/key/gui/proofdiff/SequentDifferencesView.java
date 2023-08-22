/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.proofdiff;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.util.List;
import javax.swing.*;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;

import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (31.03.23)
 */
public class SequentDifferencesView extends JPanel {
    private static final String EDITOR_TYPE = "plain/text";
    public static final String PROPERTY_LEFT = "left";
    public static final String PROPERTY_RIGHT = "right";
    private static final Logger LOGGER = LoggerFactory.getLogger(SequentDifferencesView.class);

    private final Services servicesLeft, servicesRight;

    private Sequent left, right;
    private final KeyAction actionHideCommonFormulas = new HideCommandFormulaAction();
    private final VisibleTermLabels termLabels;

    public SequentDifferencesView(Services servicesLeft, Services servicesRight,
            VisibleTermLabels termLabels) {
        this.servicesLeft = servicesLeft;
        this.servicesRight = servicesRight;
        this.termLabels = termLabels;
        var boxLayout = new BoxLayout(this, BoxLayout.Y_AXIS);
        setLayout(boxLayout);

        addPropertyChangeListener(evt -> {
            if (left != null && right != null) {
                updateView();
            }
        });

        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .addPropertyChangeListener(e -> updateView());
    }

    public Sequent getLeft() {
        return left;
    }

    public void setLeft(Sequent left) {
        if (left == null)
            return;
        var oldValue = this.left;
        this.left = left;
        firePropertyChange(PROPERTY_LEFT, oldValue, left);
    }

    public Sequent getRight() {
        return right;
    }

    public void setRight(Sequent right) {
        if (right == null)
            return;
        var oldValue = this.right;
        this.right = right;
        firePropertyChange(PROPERTY_RIGHT, oldValue, right);
    }

    private void updateView() {
        removeAll();
        SequentDifference pd =
            SequentDifference.create(servicesLeft, servicesRight, left, right, termLabels);
        fill("Antecedent Differences", pd.getAntecPairs());
        fill("Succedent Differences", pd.getSuccPairs());
        invalidate();
        revalidate();
        repaint();
        repaint();
        repaint();
    }

    private void fill(String title, List<SequentDifference.Matching> pairs) {
        Box pane = new Box(BoxLayout.Y_AXIS);
        pane.setBorder(BorderFactory.createTitledBorder(title));
        if (!pairs.isEmpty())
            add(pane);
        for (SequentDifference.Matching pair : pairs) {
            // hideCommonFormulas --> distance != 0
            if (!isHideCommonFormulas() || pair.distance > 0) { // skip formulas that have no
                // differences
                var txtL = createEditor(pair.left);
                var txtR = createEditor(pair.right);
                txtL.setAlignmentX(Component.RIGHT_ALIGNMENT);

                Box boxPair = new Box(BoxLayout.X_AXIS);
                boxPair.add(txtL);
                boxPair.add(new JSeparator(JSeparator.VERTICAL));
                boxPair.add(txtR);
                equaliseSize(txtL, txtR);
                pane.add(boxPair);
                pane.add(new JSeparator(JSeparator.HORIZONTAL));
                // txtL.setRows(3);
                // txtR.setRows(3);
                // contentPanel.add(txtL, cc);
                // contentPanel.add(txtR, cc);
                // hightlightDifferences(txtL, txtR);
            }
        }
    }

    private static void equaliseSize(JComponent txtL, JComponent txtR) {
        Dimension max = new Dimension(Math.max(txtL.getWidth(), txtR.getWidth()),
            Math.max(txtL.getHeight(), txtR.getHeight()));
        txtR.setSize(max);
        txtL.setSize(max);
        txtR.setPreferredSize(max);
        txtL.setPreferredSize(max);
    }

    protected JComponent createEditor(String content) {
        JEditorPane je = new JEditorPane(EDITOR_TYPE, content != null ? content : "");
        je.setEditable(false);
        je.setFont(UIManager.getDefaults().getFont(Config.KEY_FONT_SEQUENT_VIEW));
        JPanel textAreaPanel = new JPanel(new BorderLayout());
        textAreaPanel.setBorder(BorderFactory.createEmptyBorder(2, 2, 2, 2));
        textAreaPanel.add(je);
        return textAreaPanel;
    }

    private void highlightDifferences(JEditorPane txtL, JEditorPane txtR) {
        DefaultHighlighter df1 = new DefaultHighlighter();
        txtL.setHighlighter(df1);
        DefaultHighlighter df2 = new DefaultHighlighter();
        txtL.setHighlighter(df2);
        char[] l = txtL.getText().toCharArray();
        char[] r = txtR.getText().toCharArray();

        try {
            for (int i = 0; i < Math.min(l.length, r.length); i++) {
                int start = i;
                for (; i < Math.min(l.length, r.length); i++);
                if (start != i) {
                    df1.addHighlight(start, i,
                        new DefaultHighlighter.DefaultHighlightPainter(Color.RED));
                    df2.addHighlight(start, i,
                        new DefaultHighlighter.DefaultHighlightPainter(Color.RED));
                }
            }
        } catch (BadLocationException | NullPointerException e) {
            e.printStackTrace();
        }
    }

    public boolean isHideCommonFormulas() {
        return actionHideCommonFormulas.isSelected();
    }

    public void setHideCommonFormulas(boolean hideCommonFormulas) {
        this.actionHideCommonFormulas.setEnabled(hideCommonFormulas);
    }

    public KeyAction getActionHideCommonFormulas() {
        return actionHideCommonFormulas;
    }

    private class HideCommandFormulaAction extends KeyAction {
        public HideCommandFormulaAction() {
            setName("Hide common formulas");
            setSelected(true);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            updateView();
        }
    }
}
