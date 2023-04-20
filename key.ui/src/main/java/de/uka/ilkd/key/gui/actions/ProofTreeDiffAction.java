package de.uka.ilkd.key.gui.actions;

import bibliothek.gui.dock.common.DefaultSingleCDockable;
import bibliothek.gui.dock.common.intern.DefaultCommonDockable;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.docking.DockingHelper;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;
import de.uka.ilkd.key.gui.proofdiff.SequentDifference;
import de.uka.ilkd.key.gui.proofdiff.SequentDifferencesView;
import de.uka.ilkd.key.gui.prooftree.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.SpecNameLabel;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.strategy.termfeature.TermLabelTermFeature;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.swing.*;
import javax.swing.tree.TreePath;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.File;
import java.util.List;
import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;

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

    @Nullable
    private Proof selectProof(String s, Proof[] proofs) {
        var map = Arrays.stream(proofs).collect(Collectors.toMap(Proof::name, it -> it));
        var values = map.keySet().toArray();
        var selected = JOptionPane.showInputDialog(mainWindow, "Select a " + s + " proof for comparison",
                "Select a proof", JOptionPane.INFORMATION_MESSAGE, null, values,
                getMediator().getSelectedProof());
        if (selected != null) {
            return map.get(selected);
        }
        return null;
    }

    public void showFrame(Proof left, Proof right) {
        var panel = new ProofTreeDiffView(left, right, mainWindow.getVisibleTermLabels());
        var dockable = new DefaultSingleCDockable("proof-tree-diff", "Proof Tree Diff", panel);
        dockable.addAction(DockingHelper.translateAction(panel.getActionFindingDifferencesMatching()));
        dockable.addAction(DockingHelper.translateAction(panel.getActionFindingDifferencesString()));
        dockable.addAction(DockingHelper.translateAction(panel.getActionAutoSelect()));
        var dcd = new DefaultCommonDockable(dockable);
        mainWindow.getDockControl().getContentArea().getCenter().addDockable(dcd);
    }

    public static void main(String[] args) throws ProblemLoaderException {
        // Standalone tool for proof diffing
        if (args.length != 2) {
            //throw new IllegalArgumentException("Two proofs. not less. not more");
            args = new String[]{
                    "/tmp/orig.proof", "/tmp/label.proof"
            };
        }

        Proof first = KeYEnvironment.load(new File(args[0])).getLoadedProof();
        Proof second = KeYEnvironment.load(new File(args[1])).getLoadedProof();

        JFrame frame = new JFrame();
        frame.setLayout(new BorderLayout());
        var termLabels = new TermLabelVisibilityManager();
        termLabels.setHidden(SpecNameLabel.NAME, true);
        var panel = new ProofTreeDiffView(first, second, termLabels);
        frame.add(panel);

        var jt = new JToolBar();
        jt.add(panel.getActionFindingDifferencesMatching());
        jt.add(panel.getActionFindingDifferencesString());
        jt.add(panel.getActionAutoSelect());
        frame.add(jt, BorderLayout.NORTH);
        frame.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);
        frame.setSize(800,1000);
        frame.setVisible(true);
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

    private final KeyAction actionFindingDifferencesMatching;
    private final KeyAction actionFindingDifferencesString;

    private final KeyAction actionAutoSelect = new AutoSelectOtherNode();


    public ProofTreeDiffView(Proof left, Proof right, VisibleTermLabels termLabels) {
        this.proofLeft = left;
        this.proofRight = right;
        lastSelectedNodeRight = right.root();
        lastSelectedNodeLeft = left.root();

        actionFindingDifferencesMatching = new FindAllDifferences(
                new HasDifferenceBasedOnNonMatching(proofLeft, proofRight, termLabels));

        actionFindingDifferencesString = new FindAllDifferences(
                new HasDifferenceBasedOnLogicPrinter(proofLeft, proofRight, termLabels));


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

        var diff = new SequentDifferencesView(proofLeft.getServices(), proofRight.getServices(), termLabels);
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

    public KeyAction getActionFindingDifferencesMatching() {
        return actionFindingDifferencesMatching;
    }

    public KeyAction getActionFindingDifferencesString() {
        return actionFindingDifferencesString;
    }

    public static final IconFontProvider ICON_MAGNIFIER =
            new IconFontProvider(FontAwesomeSolid.MINUS_CIRCLE);

    public static final IconFontProvider ICON_SELECTED =
            new IconFontProvider(FontAwesomeSolid.USER_CHECK, Color.ORANGE);

    public static final IconFontProvider ICON_NO_SELECT =
            new IconFontProvider(FontAwesomeSolid.USER_CHECK, Color.GRAY);

    public KeyAction getActionAutoSelect() {
        return actionAutoSelect;
    }

    public class FindAllDifferences extends KeyAction {
        private final BiFunction<Sequent, Sequent, Boolean> isDifferent;


        public FindAllDifferences(BiFunction<Sequent, Sequent, Boolean> isDifferent) {
            this.isDifferent = isDifferent;
            setName("Find and Mark Differences using " + isDifferent.getClass().getSimpleName());
            setIcon(ICON_MAGNIFIER.get(16));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            fillDiffInformation();
            invalidate();
            repaint();
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

                if (isDifferent.apply(l.sequent(), r.sequent())) {
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
    }

    public class AutoSelectOtherNode extends KeyAction {
        public AutoSelectOtherNode() {
            setName("Auto select twin node");
            AutoSelectOtherNode.this.addPropertyChangeListener((evt) -> updateIcon());
            setSelected(autoSelectOtherNode);
            updateIcon();
        }

        private void updateIcon() {
            if (isSelected())
                setIcon(ICON_SELECTED.get(16));
            else
                setIcon(ICON_NO_SELECT.get(16));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            setAutoSelectOtherNode(isSelected());
        }
    }
}

class HasDifferenceBasedOnLogicPrinter implements BiFunction<Sequent, Sequent, Boolean> {
    private final Function<Term, String> leftPrinter;
    private final Function<Term, String> rightPrinter;
    private final VisibleTermLabels termLabels;


    HasDifferenceBasedOnLogicPrinter(Proof proofLeft, Proof proofRight, VisibleTermLabels termLabels) {
        this.leftPrinter = SequentDifference.createPrinter(proofLeft.getServices(), termLabels);
        this.rightPrinter = SequentDifference.createPrinter(proofRight.getServices(), termLabels);
        this.termLabels = termLabels;
    }


    @Override
    public Boolean apply(Sequent a, Sequent b) {
        var left = print(leftPrinter, a);
        var right = print(rightPrinter, b);
        return !left.equals(right);
    }

    private static List<String> print(Function<Term, String> printer, Sequent a) {
        var result = new ArrayList<String>(a.antecedent().size() + a.succedent().size());
        result.addAll(print(printer, a.antecedent().asList()));
        result.addAll(print(printer, a.succedent().asList()));
        return result;
    }

    private static Collection<String> print(Function<Term, String> printer, ImmutableList<SequentFormula> list) {
        return list.stream().map(it -> printer.apply(it.formula())).sorted().collect(Collectors.toList());
    }
}

class HasDifferenceBasedOnNonMatching implements BiFunction<Sequent, Sequent, Boolean> {
    private final Proof proofLeft, proofRight;
    private final VisibleTermLabels termLabels;

    HasDifferenceBasedOnNonMatching(Proof proofLeft, Proof proofRight, VisibleTermLabels termLabels) {
        this.proofLeft = proofLeft;
        this.proofRight = proofRight;
        this.termLabels = termLabels;
    }


    @Override
    public Boolean apply(Sequent left, Sequent right) {
        var s = SequentDifference.create(proofLeft.getServices(), proofRight.getServices(), left, right, termLabels);
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