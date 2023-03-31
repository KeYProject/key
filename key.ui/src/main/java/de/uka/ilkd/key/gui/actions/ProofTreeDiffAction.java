package de.uka.ilkd.key.gui.actions;

import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import bibliothek.gui.dock.common.NullMultipleCDockableFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.docking.DockingHelper;
import de.uka.ilkd.key.gui.proofdiff.SequentDifference;
import de.uka.ilkd.key.gui.proofdiff.SequentDifferencesView;
import de.uka.ilkd.key.gui.prooftree.*;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Pair;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import javax.swing.*;
import javax.swing.tree.TreePath;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (31.03.23)
 */
public class ProofTreeDiffAction extends MainWindowAction {
    public static final Logger LOGGER = LoggerFactory.getLogger(ProofTreeDiffAction.class);


    public ProofTreeDiffAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Find differences in proof tree diff");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        LOGGER.info("Action: ProofTreeDiffAction was triggered");
        var currentLoaded = mainWindow.getProofList().getModel().getLoadedProofs().toArray(new Proof[0]);
        Proof left, right = null;

        LOGGER.info("{} Proof loaded", currentLoaded.length);

        if (currentLoaded.length == 1) {
            JOptionPane.showMessageDialog(mainWindow,
                    "Only one proof is loaded. Finding differences make no sense.",
                    "Error", JOptionPane.ERROR_MESSAGE);
            return;
        } else {
            if (currentLoaded.length == 2) {
                left = currentLoaded[0];
                right = currentLoaded[1];
                LOGGER.info("Only two proofs loaded. Selecting them for diffing.");
            } else {
                LOGGER.info("Ask user for selection of proofs");
                left = selectProof("left", currentLoaded);
                if (left != null)
                    right = selectProof("right", currentLoaded);
            }
        }

        if (left != null && right != null) {
            LOGGER.info("Show diffing view");
            showFrame(left, right);
        }
    }

    private Proof selectProof(String s, Proof[] proofs) {
        return (Proof) JOptionPane.showInputDialog(mainWindow, "Select a " + s + " proof for comparison",
                "Select a proof", JOptionPane.INFORMATION_MESSAGE, null, proofs,
                getMediator().getSelectedProof());
    }

    public void showFrame(Proof left, Proof right) {
        var panel = new ProofTreeDiffView(left, right);
        var dockable = new DefaultMultipleCDockable(NullMultipleCDockableFactory.NULL, "Proof Tree Diff", panel);
        dockable.addAction(DockingHelper.translateAction(panel.getActionFindingDifferences()));
        dockable.addAction(DockingHelper.translateAction(panel.getActionAutoSelect()));
        mainWindow.getDockControl().addDockable(dockable);
    }
}

class ProofTreeDiffView extends JPanel {
    public static final String PROPERTY_SELECTED_NODE_RIGHT = "lastSelectedNodeRight";
    public static final String PROPERTY_SELECTED_NODE_LEFT = "lastSelectedNodeLeft";
    public static final String PROPERTY_AUTO_SELECT = "autoSelectOtherNode";
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofTreeDiffView.class);
    @Nonnull
    private final Proof proofRight;
    @Nonnull
    private final Proof proofLeft;
    private final ProofTreeView treeLeft;
    private final ProofTreeView treeRight;

    @Nonnull
    private Node lastSelectedNodeRight;
    @Nonnull
    private Node lastSelectedNodeLeft;

    private final MarkedNodeStyler markedNodeStyler = new MarkedNodeStyler();
    private final Map<Node, Node> pairs = new HashMap<>();

    private boolean autoSelectOtherNode = true;

    private final KeyAction actionFindingDifferences = new FindAllDifferences();
    private final KeyAction actionAutoSelect = new AutoSelectOtherNode();


    public ProofTreeDiffView(Proof left, Proof right) {
        this.proofLeft = left;
        this.proofRight = right;
        lastSelectedNodeRight = right.root();
        lastSelectedNodeLeft = left.root();

        setLayout(new BorderLayout());
        var root = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
        var splitter = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
        this.treeLeft = new ProofTreeView();
        this.treeRight = new ProofTreeView();
        final var scrollLeft = new JScrollPane(treeLeft);
        splitter.setLeftComponent(scrollLeft);
        final var scrollRight = new JScrollPane(treeRight);
        splitter.setRightComponent(scrollRight);
        splitter.setOneTouchExpandable(true);
        root.setOneTouchExpandable(true);
        splitter.setDividerLocation(.5);
        root.setDividerLocation(.7);
        treeRight.setProof(right);
        treeLeft.setProof(left);

        scrollRight.setBorder(BorderFactory.createTitledBorder("Proof: " + right.name()));
        scrollLeft.setBorder(BorderFactory.createTitledBorder("Proof: " + left.name()));

        var diff = new SequentDifferencesView(proofLeft.getServices(), proofRight.getServices());
        diff.setHideCommonFormulas(true);

        treeLeft.getDelegateView().setScrollsOnExpand(true);
        treeRight.getDelegateView().setScrollsOnExpand(true);


        treeRight.getDelegateView().addTreeSelectionListener(e -> {
            final var nodeRight = ((GUIAbstractTreeNode) e.getPath().getLastPathComponent()).getNode();
            setLastSelectedNodeRight(nodeRight);

            var nodeLeft = pairs.get(nodeRight);
            if (nodeLeft != null && autoSelectOtherNode) {
                /*var treeNode = treeLeft.getDelegateModel().find(nodeLeft);
                if (treeNode != null) {
                    final var path = new TreePath(treeNode);
                    treeLeft.getDelegateView().setSelectionPath(path);
                    treeLeft.getDelegateView().expandPath(path);
                }*/
                treeLeft.makeNodeVisible(nodeLeft);
            }
        });

        treeLeft.getDelegateView().addTreeSelectionListener(e -> {
            final var nodeLeft = ((GUIAbstractTreeNode) e.getPath().getLastPathComponent()).getNode();
            setLastSelectedNodeLeft(nodeLeft);

            var nodeRight = pairs.get(nodeLeft);
            if (nodeRight != null && autoSelectOtherNode) {
                treeRight.makeNodeVisible(nodeRight);
                /*
                var treeNode = treeRight.getDelegateModel().find(nodeLeft);
                if (treeNode != null) {
                    final var path = new TreePath(treeNode);
                    treeRight.getDelegateView().setSelectionPath(path);
                    treeRight.getDelegateView().expandPath(path);
                }*/
            }
        });

        addPropertyChangeListener(evt -> {
            diff.setLeft(lastSelectedNodeLeft.sequent());
            diff.setRight(lastSelectedNodeRight.sequent());
        });

        treeLeft.getRenderer().add(markedNodeStyler);
        treeRight.getRenderer().add(markedNodeStyler);

        treeRight.setFilter(ProofTreeViewFilter.HIDE_INTERACTIVE_GOALS, false);
        treeRight.setFilter(ProofTreeViewFilter.HIDE_CLOSED_SUBTREES, false);
        treeRight.setFilter(ProofTreeViewFilter.HIDE_INTERMEDIATE, false);

        treeLeft.setFilter(ProofTreeViewFilter.HIDE_INTERACTIVE_GOALS, false);
        treeLeft.setFilter(ProofTreeViewFilter.HIDE_CLOSED_SUBTREES, false);
        treeLeft.setFilter(ProofTreeViewFilter.HIDE_INTERMEDIATE, false);

        root.setLeftComponent(splitter);
        root.setRightComponent(new JScrollPane(diff));
        add(root);
    }

    @Nonnull
    public Node getLastSelectedNodeRight() {
        return lastSelectedNodeRight;
    }

    public void setLastSelectedNodeRight(Node lastSelectedNodeRight) {
        if (lastSelectedNodeRight == null) return;
        var oldValue = this.lastSelectedNodeRight;
        this.lastSelectedNodeRight = lastSelectedNodeRight;
        firePropertyChange(PROPERTY_SELECTED_NODE_RIGHT, oldValue, lastSelectedNodeRight);
    }

    @Nonnull
    public Node getLastSelectedNodeLeft() {
        return lastSelectedNodeLeft;
    }

    public void setLastSelectedNodeLeft(Node lastSelectedNodeLeft) {
        if (lastSelectedNodeLeft == null) return;
        var oldValue = this.lastSelectedNodeLeft;
        this.lastSelectedNodeLeft = lastSelectedNodeLeft;
        firePropertyChange(PROPERTY_SELECTED_NODE_LEFT, oldValue, lastSelectedNodeLeft);
    }

    public boolean isAutoSelectOtherNode() {
        return autoSelectOtherNode;
    }

    public void setAutoSelectOtherNode(boolean autoSelectOtherNode) {
        var oldValue = this.autoSelectOtherNode;
        this.autoSelectOtherNode = autoSelectOtherNode;
        firePropertyChange(PROPERTY_AUTO_SELECT, oldValue, autoSelectOtherNode);
    }

    public KeyAction getActionFindingDifferences() {
        return actionFindingDifferences;
    }

    public KeyAction getActionAutoSelect() {
        return actionAutoSelect;
    }

    public class FindAllDifferences extends KeyAction {
        public FindAllDifferences() {
            setName("Find and Mark Differences");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            fillDiffInformation();
            invalidate();
            repaint();
        }
    }

    public class AutoSelectOtherNode extends KeyAction {
        public AutoSelectOtherNode() {
            setName("Auto select twin node");
            setSelected(autoSelectOtherNode);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            setAutoSelectOtherNode(isSelected());
        }
    }

    private void fillDiffInformation() {
        markedNodeStyler.getMarked().clear();
        pairs.clear();

        var queue = new LinkedList<Pair<Node, Node>>();
        queue.add(new Pair<>(proofLeft.root(), proofRight.root()));

        boolean selected = false;

        while (!queue.isEmpty()) {
            var node = queue.pop();
            var l = node.first;
            var r = node.second;
            pairs.put(l, r);
            pairs.put(r, l);

            if (hasDifference(l.sequent(), r.sequent())) {
                LOGGER.info("found difference at {} and {}", l.serialNr(), r.serialNr());
                markedNodeStyler.getMarked().add(l);
                markedNodeStyler.getMarked().add(r);

                if (!selected) {
                    LOGGER.info("jump to difference at {} and {}", l.serialNr(), r.serialNr());
                    selected = true;
                    selectPath(treeLeft, l);
                    selectPath(treeRight, r);
                }
            }

            for (var i = 0; i < Math.min(l.childrenCount(), r.childrenCount()); i++) {
                queue.add(new Pair<>(l.child(i), r.child(i)));
            }
        }
    }

    private void selectPath(ProofTreeView treeView, Node n) {
        var node = treeView.getDelegateModel().find(n);
        if (node != null) {
            var path = new TreePath(node);
            treeView.getDelegateView().setSelectionPath(path);
            treeView.getDelegateView().expandPath(path);
        }
    }

    private boolean hasDifference(Sequent left, Sequent right) {
        var s = SequentDifference.create(proofLeft.getServices(), proofRight.getServices(), left, right);
        return !s.getExclusiveAntec().isEmpty() || !s.getExclusiveSucc().isEmpty();
        /* return hasDifference(left.antecedent(), right.antecedent())
                || hasDifference(left.succedent(), right.succedent());*/
    }

    private static boolean hasDifference(Semisequent left, Semisequent right) {
        return notSubset(left, right) || notSubset(right, left);
    }

    private static boolean notSubset(Semisequent a, Semisequent b) {
        for (SequentFormula fml : a.asList()) {
            if (!contains(fml, b))
                return true;
        }
        return false;
    }

    private static boolean contains(SequentFormula fml, Semisequent ss) {
        for (SequentFormula fmlB : ss.asList()) {
            if (fml.equalsModProofIrrelevancy(fmlB)) {
                return true;
            }
        }
        return false;
    }
}

class MarkedNodeStyler implements Styler<GUIAbstractTreeNode> {
    private final Set<Node> marked = new HashSet<>();

    @Override
    public void style(@Nonnull Style current, @Nonnull GUIAbstractTreeNode obj) {
        if (marked.contains(obj.getNode())) {
            current.border = Color.RED;
        }
    }

    public Set<Node> getMarked() {
        return marked;
    }
}