package de.uka.ilkd.key.gui.actions;

import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import bibliothek.gui.dock.common.NullMultipleCDockableFactory;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.proofdiff.SequentDifferencesView;
import de.uka.ilkd.key.gui.prooftree.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.beans.PropertyChangeSupport;
import java.util.HashSet;
import java.util.Set;

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
            JOptionPane.showMessageDialog(mainWindow, "Only one proof is loaded. Finding differences make no sense.",
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
        var panel = new ProofTreeDiffView(left, right, getMediator());
        var dockable = new DefaultMultipleCDockable(NullMultipleCDockableFactory.NULL, "Proof Tree Diff", panel);
        mainWindow.getDockControl().addDockable(dockable);
    }
}

class ProofTreeDiffView extends JPanel {
    public static final String PROPERTY_SELECTED_NODE_RIGHT = "lastSelectedNodeRight";
    public static final String PROPERTY_SELECTED_NODE_LEFT = "lastSelectedNodeLeft";
    @Nonnull
    private final Proof proofRight;
    @Nonnull
    private final Proof proofLeft;

    @Nonnull
    private Node lastSelectedNodeRight;
    @Nonnull
    private Node lastSelectedNodeLeft;

    private final MarkedNodeStyler markedNodeStyler = new MarkedNodeStyler();

    public ProofTreeDiffView(Proof left, Proof right, KeYMediator mediator) {
        this.proofLeft = left;
        this.proofRight = right;
        lastSelectedNodeRight = right.root();
        lastSelectedNodeLeft = left.root();

        setLayout(new BorderLayout());
        var root = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
        var splitter = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
        final var treeLeft = new ProofTreeView();
        final var treeRight = new ProofTreeView();
        final var scrollLeft = new JScrollPane(treeLeft);
        splitter.setLeftComponent(scrollLeft);
        final var scrollRight = new JScrollPane(treeRight);
        splitter.setRightComponent(scrollRight);
        splitter.setOneTouchExpandable(false);
        splitter.setDividerLocation(.5);
        root.setDividerLocation(.7);
        treeRight.setProof(right);
        treeLeft.setProof(left);

        scrollRight.setBorder(BorderFactory.createTitledBorder("Proof: " + right.name()));
        scrollLeft.setBorder(BorderFactory.createTitledBorder("Proof: " + left.name()));

        var diff = new SequentDifferencesView(mediator);
        diff.setHideCommonFormulas(true);

        treeRight.getDelegateView().addTreeSelectionListener(e ->
                setLastSelectedNodeRight(((GUIAbstractTreeNode) e.getPath().getLastPathComponent()).getNode()));

        treeLeft.getDelegateView().addTreeSelectionListener(e ->
                setLastSelectedNodeLeft(((GUIAbstractTreeNode) e.getPath().getLastPathComponent()).getNode()));

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
        root.setRightComponent(diff);
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

    public class FindAllDifferences extends KeyAction {
        public FindAllDifferences() {
        }

        @Override
        public void actionPerformed(ActionEvent e) {

        }
    }
}

class MarkedNodeStyler implements Styler<GUIAbstractTreeNode> {
    private final Set<Node> marked = new HashSet<>();

    @Override
    public void style(@Nonnull Style current, @Nonnull GUIAbstractTreeNode obj) {
        if (marked.contains(obj.getNode())) {
            current.background = Color.YELLOW;
        }
    }

    public Set<Node> getMarked() {
        return marked;
    }
}