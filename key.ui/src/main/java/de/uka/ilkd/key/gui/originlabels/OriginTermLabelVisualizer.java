/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.originlabels;

import java.awt.*;
import java.awt.event.*;
import java.util.Objects;
import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.AncestorEvent;
import javax.swing.event.AncestorListener;
import javax.swing.plaf.basic.BasicTreeUI;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.NodeInfoVisualizer;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.util.pp.UnbalancedBlocksException;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import bibliothek.gui.dock.common.DefaultSingleCDockable;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This UI component visualizes the {@link OriginTermLabel}s of a term and its sub-terms.
 *
 * @author lanzinger
 */
@NullMarked
public final class OriginTermLabelVisualizer extends NodeInfoVisualizer {

    private static final long serialVersionUID = -9190616436091589798L;

    /**
     * The background color to use to highlight a sub-term.
     */
    public final static Color HIGHLIGHT_COLOR = Color.ORANGE;

    /**
     * The title for the origin information for the selected term.
     *
     * @see #ORIGIN_TITLE
     * @see #SUBTERM_ORIGINS_TITLE
     */
    public final static String ORIGIN_INFO_TITLE = "Origin information";

    /**
     * The title for the selected term's origin.
     *
     * @see #ORIGIN_INFO_TITLE
     */
    public final static String ORIGIN_TITLE = "Origin of formula";

    /**
     * The title for the origin of the selected term's sub-terms and former sub-terms.
     *
     * @see #ORIGIN_INFO_TITLE
     */
    public final static String SUBTERM_ORIGINS_TITLE =
        "Origins of (former) subformulas and subterms";

    /**
     * The gap between a term and its origin in the tree view.
     */
    public static final int TREE_CELL_GAP = 20;

    /**
     * The gap between the window's components
     */
    public static final int COMPONENT_GAP = 20;

    /** This window's {@link TermView}. */
    private TermView view;

    /** This window tree view. */
    private JTree tree;

    /** The currently highlighted position. */
    private @Nullable PosInOccurrence highlight;

    /** The button for the {@link #nodeLinkAction} */

    private JButton nodeLinkButton;

    /**
     * Action to select {@link #getNode()} in the main window.
     *
     * @see #updateNodeLink()
     */
    private final Action nodeLinkAction = new AbstractAction() {
        private static final long serialVersionUID = -5322782759362752086L;

        @Override
        public void actionPerformed(ActionEvent e) {
            Node node = getNode();
            if (node == null) {
                // the action is only usable while the visualizer still holds its node
                throw new NullPointerException("No node available.");
            }
            KeYMediator mediator = MainWindow.getInstance().getMediator();

            if (!mediator.getSelectedProof().equals(node.proof())) {
                int choice = JOptionPane.showOptionDialog(OriginTermLabelVisualizer.this,
                    "The proof containing this node is not currently selected."
                        + " Do you want to select it?",
                    "Switch Proof?", JOptionPane.YES_NO_OPTION, JOptionPane.QUESTION_MESSAGE, null,
                    null, null);

                if (choice == 0) {
                    mediator.getSelectionModel().setSelectedProof(node.proof());
                } else {
                    return;
                }
            }

            mediator.getSelectionModel().setSelectedNode(node);
            ((DefaultSingleCDockable) MainWindow.getInstance().getDockSequent()).toFront();
        }
    };

    /**
     * Listens to rule application to call {@link #updateNodeLink()}.
     * <p>
     * The lambda invokes {@link #updateNodeLink()} on the receiver while the field is being
     * initialized (EISOP initialization check); the listener only fires after construction
     * completes, suppressed with a scoped key. The field is nulled in {@link #dispose()} to
     * release the reference.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    private @Nullable RuleAppListener ruleAppListener = event -> updateNodeLink();

    /**
     * Listens to changes to the proof to call {@link #updateNodeLink()}.
     */
    private @Nullable ProofTreeListener proofTreeListener = new ProofTreeAdapter() {

        @Override
        public void proofStructureChanged(ProofTreeEvent e) {
            updateNodeLink();
        }

        @Override
        public void proofPruned(ProofTreeEvent e) {
            updateNodeLink();
        }

        @Override
        public void proofGoalsChanged(ProofTreeEvent e) {
            updateNodeLink();
        }

        @Override
        public void proofExpanded(ProofTreeEvent e) {
            updateNodeLink();
        }
    };

    /**
     * Listens to changes to the proof to call {@link #updateNodeLink()}.
     */
    private @Nullable ProofDisposedListener proofDisposedListener = new ProofDisposedListener() {

        @Override
        public void proofDisposing(ProofDisposedEvent e) {}

        @Override
        public void proofDisposed(ProofDisposedEvent e) {
            updateNodeLink();
        }
    };

    /**
     * Services are only available while the visualizer is alive; the field is nulled in
     * {@link #dispose()} to release the reference.
     */
    private @Nullable Services services;

    /** The position of the term being shown in this window. */
    private @Nullable PosInOccurrence termPio;

    /**
     * The sequent containing the term being shown in this window; nulled in {@link #dispose()}
     * to release the reference.
     */
    private @Nullable Sequent sequent;

    /**
     * Creates a new {@link OriginTermLabelVisualizer}.
     *
     * @param pos the position of the term whose origin shall be visualized.
     * @param node the node representing the proof state for which the term's origins shall be
     *        visualized.
     * @param services services.
     * <p>
     * The constructor leaves {@code view}, {@code tree} and {@code nodeLinkButton} unset until
     * the private init methods run and configures visible components while the receiver is
     * still under initialization (EISOP initialization check), suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:initialization.fields.uninitialized",
        "nullness:method.invocation.invalid" })
    public OriginTermLabelVisualizer(@Nullable PosInOccurrence pos, Node node,
            Services services) {
        super(node,
            "Origin for node " + node.serialNr() + ": " + (pos == null ? "whole sequent"
                    : LogicPrinter.quickPrintTerm((JTerm) pos.subTerm(), services).replaceAll(
                        "\\s+",
                        " ")),
            "Node " + node.serialNr());

        this.services = services;
        this.termPio = pos;
        this.sequent = node.sequent();

        setVisible(true);
        setLayout(new BorderLayout());

        initHeadPane();

        JSplitPane bodyPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
        String borderTitle;
        if (pos == null) {
            borderTitle = "selected sequent";
        } else if (pos.isInAntec()) {
            borderTitle = "selected formula in antecedent";
        } else {
            borderTitle = "selected formula in succedent";
        }
        initTree(bodyPane, borderTitle);
        initView(bodyPane, borderTitle);

        add(bodyPane, BorderLayout.CENTER);

        addAncestorListener(new AncestorListener() {

            private boolean setup = false;

            @Override
            public void ancestorRemoved(AncestorEvent event) {
                view.removeUserSelectionHighlight();
            }

            @Override
            public void ancestorMoved(AncestorEvent event) {
                // Hide source view by default.
                if (!setup && bodyPane.getSize() != null
                        && !bodyPane.getSize().equals(new Dimension())) {
                    setup = true;

                    bodyPane.getLeftComponent().setMinimumSize(new Dimension());
                    bodyPane.getRightComponent().setMinimumSize(new Dimension());

                    bodyPane.setDividerLocation(1.0);
                    bodyPane.setResizeWeight(1.0);
                    bodyPane.setOneTouchExpandable(true);
                }

                // Repaint tree so that it conforms to the new size.
                tree.revalidate();
                tree.repaint();
            }

            @Override
            public void ancestorAdded(AncestorEvent event) {
                ancestorMoved(event);
            }
        });
    }

    @Override
    public void dispose() {
        Node node = getNode();
        if (node == null) {
            // dispose is only called once, while the visualizer still holds its node
            throw new NullPointerException("No node available.");
        }
        if (!node.proof().isDisposed()) {
            RuleAppListener currentRuleAppListener = ruleAppListener;
            if (currentRuleAppListener != null) {
                node.proof().removeRuleAppListener(currentRuleAppListener);
            }
            ProofTreeListener currentProofTreeListener = proofTreeListener;
            if (currentProofTreeListener != null) {
                node.proof().removeProofTreeListener(currentProofTreeListener);
            }
            ProofDisposedListener currentProofDisposedListener = proofDisposedListener;
            if (currentProofDisposedListener != null) {
                node.proof().removeProofDisposedListener(currentProofDisposedListener);
            }
        }

        view.removeUserSelectionHighlight();

        // These fields are only nulled to release the references once the visualizer is
        // disposed; no code path reads them afterwards.
        ruleAppListener = null;
        proofTreeListener = null;
        proofDisposedListener = null;
        services = null;
        termPio = null;
        sequent = null;

        super.dispose();
    }

    private void initHeadPane() {
        Node node = getNode();
        if (node == null) {
            // the head pane is only built while the visualizer still holds its node
            throw new NullPointerException("No node available.");
        }

        JPanel headPane = new JPanel();
        headPane.setLayout(new BoxLayout(headPane, BoxLayout.PAGE_AXIS));

        JPanel top = new JPanel();
        top.setLayout(new BoxLayout(top, BoxLayout.LINE_AXIS));
        top.add(new JLabel("Node: "));
        nodeLinkButton = new JButton();
        top.add(nodeLinkButton);
        headPane.add(top);

        JPanel bot = new JPanel();
        JLabel label = new JLabel("Proof: \"" + node.proof().name() + "\"");
        label.setMinimumSize(new Dimension(top.getWidth(), label.getMinimumSize().height));
        bot.setLayout(new BoxLayout(bot, BoxLayout.LINE_AXIS));
        bot.add(label);
        headPane.add(bot);

        nodeLinkButton.setAction(nodeLinkAction);
        updateNodeLink();

        ProofTreeListener currentProofTreeListener = proofTreeListener;
        if (currentProofTreeListener == null) {
            // initHeadPane runs before dispose() nulls the listeners
            throw new NullPointerException("No proof tree listener available.");
        }
        node.proof().addRuleAppListener(ruleAppListener);
        node.proof().addProofTreeListener(currentProofTreeListener);
        node.proof().addProofDisposedListener(proofDisposedListener);

        add(headPane, BorderLayout.PAGE_START);
    }

    private void initTree(JSplitPane bodyPane, String borderTitle) {
        DefaultTreeModel treeModel = buildModel(termPio);
        tree = new JTree(treeModel);
        tree.setCellRenderer(new CellRenderer());
        ToolTipManager.sharedInstance().registerComponent(tree);

        tree.addTreeSelectionListener(e -> {
            TreeNode source = (TreeNode) tree.getLastSelectedPathComponent();

            if (source == null || source.pos == null) {
                highlight = null;
                highlightInView(null);
            } else {
                highlight = source.pos;
                highlightInView(source.pos);
            }

            revalidate();
            repaint();
        });

        JScrollPane treeScrollPane = new JScrollPane(tree, JScrollPane.VERTICAL_SCROLLBAR_ALWAYS,
            JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);

        treeScrollPane.setBorder(new TitledBorder(borderTitle + " as tree"));

        bodyPane.add(treeScrollPane);

        treeScrollPane.addComponentListener(new ComponentAdapter() {

            @Override
            public void componentResized(ComponentEvent e) {
                tree.setSize(treeScrollPane.getViewport().getSize());
                tree.setUI(new BasicTreeUI());
            }
        });
    }

    private void initView(JSplitPane bodyPane, String borderTitle) {
        Node node = getNode();
        if (node == null) {
            // the view is only built while the visualizer still holds its node
            throw new NullPointerException("No node available.");
        }
        view = new TermView(termPio, node, MainWindow.getInstance());

        view.addMouseListener(new MouseAdapter() {

            @Override
            public void mouseClicked(MouseEvent e) {
                PosInSequent pis = view.getLastPosInSequent();

                if (pis == null || Objects.equals(highlight, pis.getPosInOccurrence())) {
                    highlight = null;
                    view.removeUserSelectionHighlight();
                    highlightInTree(null);
                } else {
                    highlight = pis.getPosInOccurrence();

                    ImmutableList<Integer> path = getPosTablePath(pis.getPosInOccurrence());
                    highlightInView(pis.getPosInOccurrence());
                    highlightInTree(getTreePath(path));

                    revalidate();
                    repaint();
                }
            }
        });

        JScrollPane viewScrollPane = new JScrollPane(view, JScrollPane.VERTICAL_SCROLLBAR_ALWAYS,
            JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
        viewScrollPane.setBorder(new TitledBorder(borderTitle));

        view.printSequent();

        bodyPane.add(viewScrollPane);

        viewScrollPane.addComponentListener(new ComponentAdapter() {

            @Override
            public void componentResized(ComponentEvent e) {
                view.printSequent();
            }
        });
    }

    private void updateNodeLink() {
        Node node = getNode();
        if (node == null) {
            // the link is only updated while the visualizer still holds its node
            throw new NullPointerException("No node available.");
        }

        if (node.proof().isDisposed() || !node.proof().find(node)) {
            nodeLinkButton.setText("DELETED NODE");
            nodeLinkAction.setEnabled(false);

            unregister(this);
        } else if (nodeLinkButton.isEnabled()) {
            nodeLinkButton.setText(node.serialNr() + ": " + node.name());
        }
    }

    /**
     * Convert a pio on the sequent to a pio on {@code this.termPio.subTerm()}.
     *
     * @param pio a pio on the sequent.
     * @return a pio on {@code this.termPio.subTerm()}.
     */
    private @Nullable PosInOccurrence convertPio(@Nullable PosInOccurrence pio) {
        PosInOccurrence currentTermPio = termPio;
        if (currentTermPio == null) {
            return pio;
        } else if (pio == null) {
            return new PosInOccurrence(currentTermPio.sequentFormula(),
                currentTermPio.posInTerm(), currentTermPio.isInAntec());
        } else {
            PosInTerm completePos = currentTermPio.posInTerm();

            org.key_project.logic.IntIterator it = pio.posInTerm().iterator();
            while (it.hasNext()) {
                completePos = completePos.down(it.next());
            }

            return new PosInOccurrence(currentTermPio.sequentFormula(), completePos,
                currentTermPio.isInAntec());
        }
    }

    private DefaultTreeModel buildModel(@Nullable PosInOccurrence pos) {
        TreeNode root = new TreeNode(pos);
        DefaultTreeModel result = new DefaultTreeModel(root);
        buildModel(root, pos, result);
        return result;
    }

    private void buildModel(TreeNode parentNode,
            @Nullable PosInOccurrence parentPos,
            DefaultTreeModel treeModel) {
        if (parentPos == null) {
            int index = 0;

            Sequent currentSequent = sequent;
            if (currentSequent == null) {
                // the model is only built while the visualizer is alive
                throw new NullPointerException("Visualizer has been disposed.");
            }

            ImmutableList<SequentFormula> children = currentSequent.antecedent().asList();

            for (SequentFormula child : children) {
                PosInOccurrence childPos =
                    new PosInOccurrence(child, PosInTerm.getTopLevel(), true);
                TreeNode childNode = new TreeNode(childPos);

                treeModel.insertNodeInto(childNode, parentNode, index);
                buildModel(childNode, childPos, treeModel);

                ++index;
            }

            children = currentSequent.succedent().asList();

            for (SequentFormula child : children) {
                PosInOccurrence childPos =
                    new PosInOccurrence(child, PosInTerm.getTopLevel(), false);
                TreeNode childNode = new TreeNode(childPos);

                treeModel.insertNodeInto(childNode, parentNode, index);
                buildModel(childNode, childPos, treeModel);

                ++index;
            }
        } else {
            var children = parentPos.subTerm().subs();

            for (int i = 0; i < children.size(); ++i) {
                TreeNode childNode = new TreeNode(parentPos.down(i));

                treeModel.insertNodeInto(childNode, parentNode, i);
                buildModel(childNode, parentPos.down(i), treeModel);
            }
        }
    }

    private void highlightInTree(@Nullable TreePath path) {
        if (path == null) {
            tree.getSelectionModel().clearSelection();
        } else {
            tree.getSelectionModel().setSelectionPath(path);
        }
    }

    private void highlightInView(@Nullable PosInOccurrence pio) {
        if (pio == null) {
            view.removeUserSelectionHighlight();
            return;
        }

        try {
            view.setUserSelectionHighlight(PosInSequent.createCfmaPos(pio));
        } catch (ArrayIndexOutOfBoundsException e) {
            // The path does not point to a valid sub-term.
            // E.g., this can happen if pretty-printing is activated and the user selects
            // the sub-term "#" of some number
            // (which only exists in the view when pretty-printing is deactivated.)
            // We simply ignore this error and do not paint any highlights.
        }
    }

    private @Nullable ImmutableList<Integer> getPosTablePath(
            @Nullable PosInOccurrence pos) {
        if (pos == null) {
            return ImmutableList.<Integer>singleton(0);
        }

        InitialPositionTable posTable = view.posTable;

        ImmutableList<Integer> path = posTable.pathForPosition(pos, view.getFilter());

        if (termPio != null) {
            if (path == null) {
                return null;
            }
            ImmutableList<Integer> prefixPath =
                posTable.pathForPosition(termPio, view.getFilter());
            if (prefixPath == null) {
                return null;
            }

            final int n = prefixPath.size();

            for (int i = 0; i < n; ++i) {
                assert Objects.equals(path.head(), prefixPath.head());

                path = path.tail();
                prefixPath = prefixPath.tail();
            }

            path = path.prepend(0).prepend(0);
        }

        return path;
    }

    private TreePath getTreePath(@Nullable ImmutableList<Integer> posTablePath) {
        if (termPio != null) {
            if (posTablePath != null) {
                posTablePath = posTablePath.tail().tail();
            }
        } else if (posTablePath != null) {
            posTablePath = posTablePath.tail();
        }

        TreeNode lastNode = (TreeNode) tree.getModel().getRoot();
        TreePath result = new TreePath(lastNode);

        if (posTablePath != null) {
            for (int i : posTablePath) {
                lastNode = (TreeNode) lastNode.getChildAt(i);

                result = result.pathByAddingChild(lastNode);
            }
        }

        return result;
    }

    private @Nullable String getTooltipText(@Nullable PosInOccurrence pio) {
        if (pio == null) {
            return null;
        }

        OriginTermLabel label =
            (OriginTermLabel) ((JTerm) pio.subTerm()).getLabel(OriginTermLabel.NAME);
        Origin origin = OriginTermLabel.getOrigin(pio);

        return "<html>Origin of selected term: <b>" + (origin == null ? "" : origin)
            + "</b><hr>Origin of (former) sub-terms:<br>"
            + (label == null ? ""
                    : label.getSubtermOrigins().stream().map(o -> o + "<br>").reduce("",
                        String::concat));
    }

    private class CellRenderer extends DefaultTreeCellRenderer {

        private static final long serialVersionUID = -7479404026154193661L;

        @Override
        public Component getTreeCellRendererComponent(JTree tree, @Nullable Object value,
                boolean selected, boolean expanded, boolean leaf, int row, boolean hasFocus) {
            if (!(value instanceof TreeNode node)) {
                // the tree only contains TreeNode elements; render anything else as the default
                return super.getTreeCellRendererComponent(tree, value, selected, expanded, leaf,
                    row, hasFocus);
            }

            PosInOccurrence pio = node.pos;
            JTerm term = node.term;
            assert pio == null || pio.subTerm().equals(term);

            BasicTreeUI ui = (BasicTreeUI) tree.getUI();

            JLabel termTextLabel = (JLabel) super.getTreeCellRendererComponent(tree, value,
                selected, expanded, leaf, row, hasFocus);
            termTextLabel.setMinimumSize(new Dimension());
            termTextLabel.setText(getShortTermText(term));
            termTextLabel.setBackground(OriginTermLabelVisualizer.this.getBackground());

            JLabel originTextLabel = new JLabel();
            Origin origin = pio == null ? null : OriginTermLabel.getOrigin(pio);

            if (origin != null) {
                originTextLabel.setText(getShortOriginText(origin));
                originTextLabel.setHorizontalAlignment(TRAILING);
            }

            JPanel result = new JPanel(new BorderLayout(TREE_CELL_GAP, TREE_CELL_GAP));

            final int indent =
                (ui.getLeftChildIndent() + ui.getRightChildIndent()) * node.getLevel();

            result.setPreferredSize(
                new Dimension(tree.getWidth() - indent, super.getPreferredSize().height));

            result.add(termTextLabel, BorderLayout.LINE_START);
            result.add(originTextLabel, BorderLayout.LINE_END);

            result.setBorder(BorderFactory.createLineBorder(Color.BLACK));
            result.setBackground(Color.WHITE);

            result.setToolTipText(OriginTermLabelVisualizer.this.getTooltipText(pio));

            return result;
        }

        private String getShortOriginText(Origin origin) {
            return origin.specType.toString();
        }

        private String getShortTermText(@Nullable JTerm term) {
            String text;

            Sequent currentSequent = sequent;
            Services currentServices = services;
            if (currentSequent == null || currentServices == null) {
                // the renderer is only used while the visualizer has not been disposed
                throw new NullPointerException("Visualizer has been disposed.");
            }

            if (term == null) {
                text = LogicPrinter.quickPrintSequent(currentSequent, currentServices);
            } else {
                text = LogicPrinter.quickPrintTerm(term, currentServices);
            }

            int endIndex = text.indexOf('\n');

            if (endIndex != text.length() - 1 && endIndex != -1) {
                return text.substring(0, endIndex).replaceAll("\\s+", " ") + " ...";
            } else {
                return text.replaceAll("\\s+", " ");
            }
        }
    }

    private static class TreeNode extends DefaultMutableTreeNode {
        private static final long serialVersionUID = -406981141537547226L;
        private final @Nullable PosInOccurrence pos;
        private @Nullable JTerm term;

        private TreeNode(@Nullable PosInOccurrence pos) {
            super();
            this.pos = pos;

            if (pos != null) {
                this.term = (JTerm) pos.subTerm();
            }
        }
    }

    private static class TermViewLogicPrinter extends SequentViewLogicPrinter {
        private final @Nullable PosInOccurrence pos;

        TermViewLogicPrinter(@Nullable PosInOccurrence pos, NotationInfo ni,
                Services services) {
            super(ni, services, PosTableLayouter.positionTable(), new TermLabelVisibilityManager());
            this.pos = pos;
        }

        @Override
        public void printFilteredSequent(SequentPrintFilter filter) {
            try {
                ImmutableList<SequentPrintFilterEntry> antec = filter.getFilteredAntec();
                ImmutableList<SequentPrintFilterEntry> succ = filter.getFilteredSucc();
                if (antec == null || succ == null) {
                    // the visualizer's printer is only invoked with a complete filter
                    throw new NullPointerException(
                        "Incomplete sequent filter for term view printing.");
                }
                layouter.markStartSub();
                layouter.startTerm(antec.size() + succ.size());
                layouter.beginC(1).ind();
                printSemisequent(antec);

                if (pos == null) {
                    layouter.brk(1, -1);
                    printSequentArrow();
                    layouter.brk();
                }

                printSemisequent(succ);

                layouter.markEndSub();
                layouter.end();
            } catch (UnbalancedBlocksException e) {
                throw new RuntimeException("Unbalanced blocks in pretty printer:\n" + e);
            }
        }
    }

    private class TermView extends SequentView {
        private static final long serialVersionUID = -8328975160581938309L;
        private InitialPositionTable posTable = new InitialPositionTable();
        private final Node node;

        /**
         * The view configures itself with printer and filter calls while the receiver is still
         * under initialization (EISOP initialization check); the effects only take place after
         * construction completes, suppressed with a scoped key. Services can only be {@code null}
         * after the visualizer was disposed.
         */
        @SuppressWarnings("nullness:method.invocation.invalid")
        TermView(@Nullable PosInOccurrence pos, Node node,
                MainWindow mainWindow) {
            super(mainWindow);
            this.node = node;

            final NotationInfo ni = new NotationInfo();
            Services currentServices = services;
            if (currentServices == null) {
                // the term view is only constructed while the visualizer is still alive
                throw new NullPointerException("No services available for the term view.");
            }
            ni.refresh(currentServices, NotationInfo.DEFAULT_PRETTY_SYNTAX,
                NotationInfo.DEFAULT_UNICODE_ENABLED, NotationInfo.DEFAULT_HIDE_PACKAGE_PREFIX);

            setLogicPrinter(new TermViewLogicPrinter(pos, ni, currentServices));

            if (pos != null) {
                setFilter(new ShowSelectedSequentPrintFilter(pos), true);
            } else {
                setFilter(new IdentitySequentPrintFilter(), true);
            }
        }

        @Override
        protected synchronized @Nullable PosInSequent getPosInSequent(@Nullable Point p) {
            PosInSequent pis = super.getPosInSequent(p);
            PosInOccurrence pio = convertPio(pis == null ? null : pis.getPosInOccurrence());
            return pio == null ? null : PosInSequent.createCfmaPos(pio);
        }

        /**
         * Returns the tool tip text for the given event.
         *
         * <p>
         * No tool tip is shown when the position does not lie on a formula, reported as
         * {@code null}; the JDK declares a non-null return although {@code null} is how
         * {@link ToolTipManager} disables a tool tip, suppressed with a scoped key.
         */
        @SuppressWarnings("nullness:override.return.invalid")
        @Override
        public @Nullable String getToolTipText(MouseEvent event) {
            PosInSequent pis = getPosInSequent(event.getPoint());

            if (pis == null) {
                return null;
            }

            return OriginTermLabelVisualizer.this.getTooltipText(pis.getPosInOccurrence());
        }

        @Override
        public void setUserSelectionHighlight(PosInSequent pis) {
            ImmutableList<Integer> path =
                getPosTablePath(pis == null ? null : pis.getPosInOccurrence());
            if (path == null) {
                return;
            }
            Range range = view.posTable.rangeForPath(path);
            range = new Range(range.start() + 1, range.end() + 1);
            pis.setBounds(range);

            super.setUserSelectionHighlight(pis);
        }

        @Override
        public void setUserSelectionHighlight(Point point) {
            super.setUserSelectionHighlight(point);
        }

        @Override
        public void removeUserSelectionHighlight() {
            super.removeUserSelectionHighlight();
        }

        @Override
        public String getTitle() {
            return "Selected term";
        }

        @Override
        public boolean isMainSequentView() {
            return false;
        }

        @Override
        public final synchronized void printSequent() {
            updateSequent(node);
            InitialPositionTable initialPositionTable = getInitialPositionTable();
            if (initialPositionTable != null) {
                posTable = initialPositionTable;
            }

            updateHidingProperty();
        }
    }
}
