/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;
import javax.swing.tree.TreeSelectionModel;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.lemma.GeneratedLemma;
import de.uka.ilkd.key.rule.lemma.GeneratedLemmaRegistry;
import de.uka.ilkd.key.rule.lemma.LemmaProver;

import org.key_project.logic.Name;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Shows, for a single proof, the lemmas it depends on that were introduced by
 * {@link de.uka.ilkd.key.rule.lemma.LemmaTacletGenerator lemma generators} (see the transparent
 * mode of the One Step Simplifier). The lemmas are grouped by generator and, within a generator,
 * collapsed by content, so that the many introduction-point-distinct instances of the same
 * simplification appear as one row with a count.
 *
 * <p>
 * From here the user can load selected lemmas as side proofs (into the same proof environment,
 * where they become visible and provable) or batch-discharge all lemmas of a generator: each
 * obligation is proved with a step bound, those that do not close are kept for manual work, and
 * the obligation proofs can optionally be saved.
 */
public final class LemmaDependencyPanel extends JPanel {

    private static final long serialVersionUID = 1L;
    private static final Logger LOGGER = LoggerFactory.getLogger(LemmaDependencyPanel.class);

    private static final int DEFAULT_MAX_STEPS = 10000;
    private static final int MAX_LABEL_LENGTH = 90;

    private final KeYMediator mediator;
    private final DefaultMutableTreeNode root = new DefaultMutableTreeNode();
    private final DefaultTreeModel treeModel = new DefaultTreeModel(root);
    private final JTree tree = new JTree(treeModel);
    private final JButton loadButton = new JButton("Load selected as side proofs");
    private final JButton proveAllButton = new JButton("Prove all lemmas...");
    private @Nullable Proof proof;
    private @Nullable Runnable onLoaded;
    private @Nullable Runnable onStatusChanged;

    public LemmaDependencyPanel(KeYMediator mediator) {
        super(new BorderLayout());
        this.mediator = mediator;

        tree.setRootVisible(false);
        tree.setShowsRootHandles(true);
        tree.getSelectionModel()
                .setSelectionMode(TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION);
        tree.addTreeSelectionListener(e -> updateButtons());

        final JScrollPane scrollPane = new JScrollPane(tree);
        scrollPane.setBorder(new TitledBorder("Lemmas this proof depends on"));
        add(scrollPane, BorderLayout.CENTER);

        loadButton.addActionListener(e -> loadSelected());
        proveAllButton.addActionListener(e -> proveAll());
        final JPanel buttons = new JPanel(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        buttons.add(proveAllButton);
        buttons.add(loadButton);
        add(buttons, BorderLayout.SOUTH);

        updateButtons();
    }

    /**
     * Sets an action to run after lemmas have been loaded as side proofs (e.g. to close the
     * enclosing dialog).
     */
    public void setOnLoaded(Runnable onLoaded) {
        this.onLoaded = onLoaded;
    }

    /**
     * Sets an action to run after the proven status of lemmas may have changed (e.g. to refresh
     * the enclosing dialog's proof-status display).
     */
    public void setOnStatusChanged(Runnable onStatusChanged) {
        this.onStatusChanged = onStatusChanged;
    }

    /**
     * Shows the lemma dependencies of the given proof (clears the view for {@code null} or a
     * proof without generated lemmas).
     */
    public void setProof(@Nullable Proof proof) {
        this.proof = proof;
        refresh();
    }

    private void refresh() {
        root.removeAllChildren();
        if (proof != null) {
            final GeneratedLemmaRegistry registry = GeneratedLemmaRegistry.getIfPresent(proof);
            if (registry != null) {
                for (final Map.Entry<Name, List<GeneratedLemma>> gen : registry
                        .getLemmasByGenerator().entrySet()) {
                    final DefaultMutableTreeNode genNode =
                        new DefaultMutableTreeNode(new GeneratorRow(gen.getKey(), gen.getValue()));
                    for (final List<GeneratedLemma> group : GeneratedLemmaRegistry
                            .groupByContent(gen.getValue()).values()) {
                        genNode.add(new DefaultMutableTreeNode(new ContentRow(group)));
                    }
                    root.add(genNode);
                }
            }
        }
        treeModel.reload();
        for (int i = 0; i < tree.getRowCount(); i++) {
            tree.expandRow(i);
        }
        updateButtons();
    }

    private void updateButtons() {
        final boolean hasLemmas = root.getChildCount() > 0;
        proveAllButton.setEnabled(hasLemmas);
        loadButton.setEnabled(!selectedLemmas().isEmpty());
    }

    /** Collects the lemmas of the selected tree nodes (generator or content rows). */
    private List<GeneratedLemma> selectedLemmas() {
        final Set<GeneratedLemma> result = new LinkedHashSet<>();
        final TreePath[] paths = tree.getSelectionPaths();
        if (paths != null) {
            for (final TreePath path : paths) {
                final Object node =
                    ((DefaultMutableTreeNode) path.getLastPathComponent()).getUserObject();
                if (node instanceof GeneratorRow row) {
                    result.addAll(row.lemmas);
                } else if (node instanceof ContentRow row) {
                    result.addAll(row.lemmas);
                }
            }
        }
        return new ArrayList<>(result);
    }

    private List<GeneratedLemma> allLemmas() {
        final List<GeneratedLemma> all = new ArrayList<>();
        for (int i = 0; i < root.getChildCount(); i++) {
            final Object row =
                ((DefaultMutableTreeNode) root.getChildAt(i)).getUserObject();
            if (row instanceof GeneratorRow gen) {
                all.addAll(gen.lemmas);
            }
        }
        return all;
    }

    private void loadSelected() {
        final List<GeneratedLemma> selected = selectedLemmas();
        if (selected.isEmpty()) {
            return;
        }
        Proof first = null;
        for (final GeneratedLemma lemma : selected) {
            // register the obligation in the environment so the user can work on it; the user
            // interface picks it up via the environment listener and adds it to the task tree
            final Proof po = lemma.registerInEnvironment().getFirstProof();
            if (first == null) {
                first = po;
            }
        }
        if (first != null) {
            mediator.getSelectionModel().setSelectedProof(first);
        }
        if (onLoaded != null) {
            onLoaded.run();
        }
    }

    private void proveAll() {
        final List<GeneratedLemma> lemmas = allLemmas();
        if (lemmas.isEmpty()) {
            return;
        }
        final ProveAllOptions options = ProveAllOptions.ask(this, lemmas.size());
        if (options == null) {
            return;
        }

        proveAllButton.setEnabled(false);
        loadButton.setEnabled(false);
        mediator.stopInterface(true);
        new SwingWorker<LemmaProver.Result, Void>() {
            @Override
            protected LemmaProver.Result doInBackground() throws Exception {
                return LemmaProver.proveAll(lemmas, options.maxSteps(), options.saveDir());
            }

            @Override
            protected void done() {
                mediator.startInterface(true);
                try {
                    final LemmaProver.Result result = get();
                    JOptionPane.showMessageDialog(LemmaDependencyPanel.this,
                        result.proven().size() + " of " + lemmas.size()
                            + " lemma(s) proved, " + result.remaining().size()
                            + " left open"
                            + (options.saveDir() != null
                                    ? ", " + result.saved() + " proof(s) saved to "
                                        + options.saveDir()
                                    : "")
                            + ".",
                        "Prove Lemmas", JOptionPane.INFORMATION_MESSAGE);
                } catch (Exception e) {
                    LOGGER.error("batch proving of lemmas failed", e);
                    JOptionPane.showMessageDialog(LemmaDependencyPanel.this,
                        "Batch proving failed:\n" + e.getMessage(), "Prove Lemmas",
                        JOptionPane.ERROR_MESSAGE);
                }
                refresh();
                // proving lemmas may have turned the depending proof from "closed but lemmas
                // left" into "closed". Recompute the status explicitly (robust against the
                // order in which proof-tree listeners handled the obligation-closed events) and
                // let the enclosing dialog refresh its status display.
                if (proof != null) {
                    proof.mgt().updateProofStatus();
                }
                if (onStatusChanged != null) {
                    onStatusChanged.run();
                }
            }
        }.execute();
    }

    private static String truncate(String s) {
        final String oneLine = s.replace('\n', ' ');
        return oneLine.length() <= MAX_LABEL_LENGTH ? oneLine
                : oneLine.substring(0, MAX_LABEL_LENGTH - 1) + "…";
    }

    private static String status(List<GeneratedLemma> lemmas) {
        int proven = 0;
        int created = 0;
        for (final GeneratedLemma lemma : lemmas) {
            if (lemma.isProven()) {
                proven++;
            } else if (lemma.isSoundnessProofPresent()) {
                created++;
            }
        }
        final StringBuilder sb = new StringBuilder();
        sb.append(proven).append('/').append(lemmas.size()).append(" proven");
        if (created > 0) {
            sb.append(", ").append(created).append(" open");
        }
        return sb.toString();
    }

    /** A generator grouping node. */
    private record GeneratorRow(Name generator, List<GeneratedLemma> lemmas) {
        @Override
        public String toString() {
            final int distinct = GeneratedLemmaRegistry.groupByContent(lemmas).size();
            return generator + " — " + lemmas.size() + " lemma(s), " + distinct
                + " distinct (" + status(lemmas) + ")";
        }
    }

    /** A content-collapsed group of lemmas denoting the same simplification. */
    private record ContentRow(List<GeneratedLemma> lemmas) {
        @Override
        public String toString() {
            final String label = truncate(lemmas.get(0).contentKey());
            return (lemmas.size() > 1 ? "×" + lemmas.size() + "  " : "") + label
                + "   [" + status(lemmas) + "]";
        }
    }

    /** Options gathered from the user before a batch proving run. */
    private record ProveAllOptions(int maxSteps, @Nullable Path saveDir) {
        static @Nullable ProveAllOptions ask(java.awt.Component parent, int count) {
            final JSpinner steps = new JSpinner(
                new SpinnerNumberModel(DEFAULT_MAX_STEPS, 100, 1_000_000, 1000));
            final JCheckBox save = new JCheckBox("Save obligation proofs to a directory");
            final JPanel panel = new JPanel(new java.awt.GridLayout(0, 1, 4, 4));
            panel.add(new JLabel("Prove all " + count
                + " lemma(s); lemmas not closing within the step bound stay open."));
            final JPanel stepsPanel = new JPanel(new FlowLayout(FlowLayout.LEFT, 5, 0));
            stepsPanel.add(new JLabel("Max. automatic steps per lemma:"));
            stepsPanel.add(steps);
            panel.add(stepsPanel);
            panel.add(save);

            final int choice = JOptionPane.showConfirmDialog(parent, panel, "Prove Lemmas",
                JOptionPane.OK_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE);
            if (choice != JOptionPane.OK_OPTION) {
                return null;
            }
            Path dir = null;
            if (save.isSelected()) {
                final JFileChooser chooser = new JFileChooser();
                chooser.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
                chooser.setDialogTitle("Directory to save lemma proofs");
                if (chooser.showSaveDialog(parent) != JFileChooser.APPROVE_OPTION) {
                    return null;
                }
                dir = chooser.getSelectedFile().toPath();
            }
            return new ProveAllOptions((Integer) steps.getValue(), dir);
        }
    }
}
