/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import bibliothek.gui.dock.common.DefaultSingleCDockable;

/**
 * This UI component visualizes the {@link OriginTermLabel}s of a term and its sub-terms.
 *
 * @author lanzinger
 */
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
    private PosInOccurrence highlight;

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
            KeYMediator mediator = MainWindow.getInstance().getMediator();

            if (!mediator.getSelectedProof().equals(getNode().proof())) {
                int choice = JOptionPane.showOptionDialog(OriginTermLabelVisualizer.this,
                    "The proof containing this node is not currently selected."
                        + " Do you want to select it?",
                    "Switch Proof?", JOptionPane.YES_NO_OPTION, JOptionPane.QUESTION_MESSAGE, null,
                    null, null);

                if (choice == 0) {
                    mediator.setProof(getNode().proof());
                } else {
                    return;
                }
            }

            mediator.getSelectionModel().setSelectedNode(getNode());
            ((DefaultSingleCDockable) MainWindow.getInstance().getDockSequent()).toFront();
        }
    };

    /**
     * Listens to rule application to call {@link #updateNodeLink()}.
     */
    private RuleAppListener ruleAppListener = event -> updateNodeLink();

    /**
     * Listens to changes to the proof to call {@link #updateNodeLink()}.
     */
    private ProofTreeListener proofTreeListener = new ProofTreeAdapter() {

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
    private ProofDisposedListener proofDisposedListener = new ProofDisposedListener() {

        @Override
        public void proofDisposing(ProofDisposedEvent e) {}

        @Override
        public void proofDisposed(ProofDisposedEvent e) {
            updateNodeLink();
        }
    };

    /** services */
    private Services services;

    /** The position of the term being shown in this window. */
    private PosInOccurrence termPio;

    /** The sequent containing the term being shown in this window. */
    private Sequent sequent;

    /**
     * Creates a new {@link OriginTermLabelVisualizer}.
     *
     * @param pos the position of the term whose origin shall be visualized.
     * @param node the node representing the proof state for which the term's origins shall be
     *        visualized.
     * @param services services.
     */
    public OriginTermLabelVisualizer(PosInOccurrence pos, Node node, Services services) {
        super(node,
            "Origin for node " + node.serialNr() + ": " + (pos == null ? "whole sequent"
                    : LogicPrinter.quickPrintTerm(pos.subTerm(), services).replaceAll("\\s+", " ")),
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
        if (!getNode().proof().isDisposed()) {
            getNode().proof().removeRuleAppListener(ruleAppListener);
            getNode().proof().removeProofTreeListener(proofTreeListener);
            getNode().proof().removeProofDisposedListener(proofDisposedListener);
        }

        view.removeUserSelectionHighlight();

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

        JPanel headPane = new JPanel();
        headPane.setLayout(new BoxLayout(headPane, BoxLayout.PAGE_AXIS));

        JPanel top = new JPanel();
        top.setLayout(new BoxLayout(top, BoxLayout.LINE_AXIS));
        top.add(new JLabel("Node: "));
        nodeLinkButton = new JButton();
        top.add(nodeLinkButton);
        headPane.add(top);

        JPanel bot = new JPanel();
        JLabel label = new JLabel("Proof: \"" + node.proof().name().toString() + "\"");
        label.setMinimumSize(new Dimension(top.getWidth(), label.getMinimumSize().height));
        bot.setLayout(new BoxLayout(bot, BoxLayout.LINE_AXIS));
        bot.add(label);
        headPane.add(bot);

        nodeLinkButton.setAction(nodeLinkAction);
        updateNodeLink();

        node.proof().addRuleAppListener(ruleAppListener);
        node.proof().addProofTreeListener(proofTreeListener);
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
        view = new TermView(termPio, getNode(), MainWindow.getInstance());

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
    private PosInOccurrence convertPio(PosInOccurrence pio) {
        if (termPio == null) {
            return pio;
        } else if (pio == null) {
            return new PosInOccurrence(termPio.sequentFormula(), termPio.posInTerm(),
                termPio.isInAntec());
        } else {
            PosInTerm completePos = termPio.posInTerm();

            IntIterator it = pio.posInTerm().iterator();
            while (it.hasNext()) {
                completePos = completePos.down(it.next());
            }

            return new PosInOccurrence(termPio.sequentFormula(), completePos, termPio.isInAntec());
        }
    }

    private DefaultTreeModel buildModel(PosInOccurrence pos) {
        TreeNode root = new TreeNode(pos);
        DefaultTreeModel result = new DefaultTreeModel(root);
        buildModel(root, pos, result);
        return result;
    }

    private void buildModel(TreeNode parentNode, PosInOccurrence parentPos,
            DefaultTreeModel treeModel) {
        if (parentPos == null) {
            int index = 0;

            ImmutableList<SequentFormula> children = sequent.antecedent().asList();

            for (SequentFormula child : children) {
                PosInOccurrence childPos =
                    new PosInOccurrence(child, PosInTerm.getTopLevel(), true);
                TreeNode childNode = new TreeNode(childPos);

                treeModel.insertNodeInto(childNode, parentNode, index);
                buildModel(childNode, childPos, treeModel);

                ++index;
            }

            children = sequent.succedent().asList();

            for (SequentFormula child : children) {
                PosInOccurrence childPos =
                    new PosInOccurrence(child, PosInTerm.getTopLevel(), false);
                TreeNode childNode = new TreeNode(childPos);

                treeModel.insertNodeInto(childNode, parentNode, index);
                buildModel(childNode, childPos, treeModel);

                ++index;
            }
        } else {
            ImmutableArray<Term> children = parentPos.subTerm().subs();

            for (int i = 0; i < children.size(); ++i) {
                TreeNode childNode = new TreeNode(parentPos.down(i));

                treeModel.insertNodeInto(childNode, parentNode, i);
                buildModel(childNode, parentPos.down(i), treeModel);
            }
        }
    }

    private void highlightInTree(TreePath path) {
        tree.getSelectionModel().setSelectionPath(path);
    }

    private void highlightInView(PosInOccurrence pio) {
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

    private ImmutableList<Integer> getPosTablePath(PosInOccurrence pos) {
        if (pos == null) {
            return ImmutableSLList.<Integer>nil().prepend(0);
        }

        InitialPositionTable posTable = view.posTable;

        ImmutableList<Integer> path = posTable.pathForPosition(pos, view.getFilter());

        if (termPio != null) {
            ImmutableList<Integer> prefixPath = posTable.pathForPosition(termPio, view.getFilter());

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

    private TreePath getTreePath(ImmutableList<Integer> posTablePath) {
        if (termPio != null) {
            posTablePath = posTablePath.tail().tail();
        } else {
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

    private String getTooltipText(PosInOccurrence pio) {
        if (pio == null) {
            return null;
        }

        OriginTermLabel label = (OriginTermLabel) pio.subTerm().getLabel(OriginTermLabel.NAME);
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
        public Component getTreeCellRendererComponent(JTree tree, Object value, boolean selected,
                boolean expanded, boolean leaf, int row, boolean hasFocus) {
            TreeNode node = (TreeNode) value;

            PosInOccurrence pio = node.pos;
            Term term = node.term;
            assert pio.subTerm().equals(term);

            BasicTreeUI ui = (BasicTreeUI) tree.getUI();

            JLabel termTextLabel = (JLabel) super.getTreeCellRendererComponent(tree, value,
                selected, expanded, leaf, row, hasFocus);
            termTextLabel.setMinimumSize(new Dimension());
            termTextLabel.setText(getShortTermText(term));
            termTextLabel.setBackground(OriginTermLabelVisualizer.this.getBackground());

            JLabel originTextLabel = new JLabel();
            Origin origin = OriginTermLabel.getOrigin(pio);

            if (origin != null) {
                originTextLabel.setText(getShortOriginText(origin));
                originTextLabel.setHorizontalAlignment(SwingConstants.TRAILING);
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

        private String getShortTermText(Term term) {
            String text;

            if (term == null) {
                text = LogicPrinter.quickPrintSequent(sequent, services);
            } else {
                text = LogicPrinter.quickPrintTerm(term, services);
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
        private final PosInOccurrence pos;
        private Term term;

        private TreeNode(PosInOccurrence pos) {
            super(pos);
            this.pos = pos;

            if (pos != null) {
                this.term = pos.subTerm();
            }
        }
    }

    private static class TermViewLogicPrinter extends SequentViewLogicPrinter {
        private final PosInOccurrence pos;

        TermViewLogicPrinter(PosInOccurrence pos, NotationInfo ni, Services services) {
            super(ni, services, PosTableLayouter.positionTable(), new TermLabelVisibilityManager());
            this.pos = pos;
        }

        @Override
        public void printFilteredSequent(SequentPrintFilter filter) {
            try {
                ImmutableList<SequentPrintFilterEntry> antec = filter.getFilteredAntec();
                ImmutableList<SequentPrintFilterEntry> succ = filter.getFilteredSucc();
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

        TermView(PosInOccurrence pos, Node node, MainWindow mainWindow) {
            super(mainWindow);
            this.node = node;

            final NotationInfo ni = new NotationInfo();
            if (services != null) {
                ni.refresh(services, NotationInfo.DEFAULT_PRETTY_SYNTAX,
                    NotationInfo.DEFAULT_UNICODE_ENABLED);
            }

            setLogicPrinter(new TermViewLogicPrinter(pos, ni, services));

            if (pos != null) {
                setFilter(new ShowSelectedSequentPrintFilter(pos), true);
            } else {
                setFilter(new IdentitySequentPrintFilter(), true);
            }
        }

        @Override
        protected synchronized PosInSequent getPosInSequent(Point p) {
            PosInSequent pis = super.getPosInSequent(p);
            PosInOccurrence pio = convertPio(pis == null ? null : pis.getPosInOccurrence());
            return pio == null ? null : PosInSequent.createCfmaPos(pio);
        }

        @Override
        public String getToolTipText(MouseEvent event) {
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
            posTable = getInitialPositionTable();

            updateHidingProperty();
        }
    }
}
