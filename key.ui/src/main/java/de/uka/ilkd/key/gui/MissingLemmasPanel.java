/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.FlowLayout;
import java.util.List;
import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.rule.lemma.GeneratedLemma;
import de.uka.ilkd.key.rule.lemma.GeneratedLemmaRegistry;

import org.jspecify.annotations.Nullable;

/**
 * Panel listing the generated lemmas that a proof still depends on but whose soundness has not
 * yet been established (see {@link GeneratedLemmaRegistry#getMissingLemmas()}). The user can
 * select individual entries or all of them and load their soundness proof obligations as side
 * proofs into the same proof environment, where they become visible and provable in the KeY GUI.
 *
 * @see de.uka.ilkd.key.rule.lemma.OssLemmaIntroductionRule
 */
public final class MissingLemmasPanel extends JPanel {

    private static final long serialVersionUID = 1L;

    private final KeYMediator mediator;
    private final DefaultListModel<GeneratedLemma> model = new DefaultListModel<>();
    private final JList<GeneratedLemma> lemmaList = new JList<>(model);
    private final JButton proveButton = new JButton("Load selected as side proofs");
    private final JButton selectAllButton = new JButton("Select all");
    private @Nullable Proof proof;
    private @Nullable Runnable onLoaded;

    public MissingLemmasPanel(KeYMediator mediator) {
        super(new BorderLayout());
        this.mediator = mediator;

        lemmaList.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
        lemmaList.setCellRenderer(new LemmaCellRenderer());
        lemmaList.addListSelectionListener(e -> updateButtons());

        final JScrollPane scrollPane = new JScrollPane(lemmaList);
        scrollPane
                .setBorder(new TitledBorder("Generated lemmas without a (closed) soundness proof"));
        add(scrollPane, BorderLayout.CENTER);

        selectAllButton.addActionListener(e -> {
            if (model.getSize() > 0) {
                lemmaList.setSelectionInterval(0, model.getSize() - 1);
            }
        });
        proveButton.addActionListener(e -> loadSelected());

        final JPanel buttonPanel = new JPanel(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        buttonPanel.add(selectAllButton);
        buttonPanel.add(proveButton);
        add(buttonPanel, BorderLayout.SOUTH);

        updateButtons();
    }

    /**
     * Shows the missing lemmas of the given proof (or clears the list if the proof is
     * {@code null} or has generated no lemmas).
     *
     * @param proof the proof whose missing lemmas to display
     */
    public void setProof(Proof proof) {
        this.proof = proof;
        refresh();
    }

    /**
     * Sets an action to run after lemmas have been loaded as side proofs (e.g. to close the
     * enclosing dialog).
     *
     * @param onLoaded the action, or {@code null} for none
     */
    public void setOnLoaded(Runnable onLoaded) {
        this.onLoaded = onLoaded;
    }

    private void refresh() {
        model.clear();
        if (proof != null) {
            final GeneratedLemmaRegistry registry = GeneratedLemmaRegistry.getIfPresent(proof);
            if (registry != null) {
                for (final GeneratedLemma lemma : registry.getMissingLemmas()) {
                    model.addElement(lemma);
                }
            }
        }
        updateButtons();
    }

    private void updateButtons() {
        selectAllButton.setEnabled(model.getSize() > 0);
        proveButton.setEnabled(!lemmaList.getSelectedValuesList().isEmpty());
    }

    private void loadSelected() {
        final List<GeneratedLemma> selected = lemmaList.getSelectedValuesList();
        if (selected.isEmpty()) {
            return;
        }
        Proof firstLoaded = null;
        for (final GeneratedLemma lemma : selected) {
            // creating the soundness proof registers it in the proof environment; the user
            // interface listens on the environment and adds it to the task tree, so the panel
            // must not register it a second time (that produced duplicate task-tree entries)
            final ProofAggregate aggregate = lemma.getOrCreateSoundnessProofAggregate();
            if (firstLoaded == null) {
                firstLoaded = aggregate.getFirstProof();
            }
        }
        if (firstLoaded != null) {
            mediator.getSelectionModel().setSelectedProof(firstLoaded);
        }
        if (onLoaded != null) {
            onLoaded.run();
        }
    }

    private static final class LemmaCellRenderer extends DefaultListCellRenderer {
        private static final long serialVersionUID = 1L;

        @Override
        public Component getListCellRendererComponent(JList<?> list, Object value, int index,
                boolean isSelected, boolean cellHasFocus) {
            final Component result = super.getListCellRendererComponent(list, value, index,
                isSelected, cellHasFocus);
            if (value instanceof GeneratedLemma lemma && result instanceof JLabel label) {
                final String status;
                if (!lemma.isSoundnessProofPresent()) {
                    status = "soundness proof obligation not yet created";
                } else if (lemma.isProven()) {
                    status = "proven";
                } else {
                    status = "soundness proof open";
                }
                label.setText(lemma.taclet().name() + "  (" + status + ")");
            }
            return result;
        }
    }
}
