package de.uka.ilkd.key.gui.originlabels;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.pp.UnbalancedBlocksException;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.plaf.basic.BasicTreeUI;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;
import java.awt.*;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.IOException;

/**
 * This window visualizes the {@link OriginTermLabel}s of a term and its sub-terms.
 *
 * @author lanzinger
 */
public final class OriginTermLabelWindow extends JFrame {

    private static final long serialVersionUID = -2791483814174192622L;

    /**
     * The window's initial width.
     */
    public static final int WIDTH = 1280;

    /**
     * The window's initial height.
     */
    public static final int HEIGHT = 720;

    /**
     * The background color to use to highlight a sub-term.
     */
    public static final Color HIGHLIGHT_COLOR = Color.ORANGE;

    /**
     * The title of the tree view.
     */
    public static final String TREE_TITLE = "Selected formula as tree";

    /**
     * The title of the term view.
     */
    public static final String VIEW_TITLE = "Selected formula";

    /**
     * The title for the origin information for the selected term.
     *
     * @see #ORIGIN_TITLE
     * @see #SUBTERM_ORIGINS_TITLE
     */
    public static final String ORIGIN_INFO_TITLE = "Origin information";

    /**
     * The title for the selected term's origin.
     *
     * @see #ORIGIN_INFO_TITLE
     */
    public static final String ORIGIN_TITLE = "Origin of formula";

    /**
     * The title for the origin of the selected term's sub-terms and former sub-terms.
     *
     * @see #ORIGIN_INFO_TITLE
     */
    public static final String SUBTERM_ORIGINS_TITLE = "Origins of (former) subformulas and subterms";

    /**
     * The gap between a term and its origin in the tree view.
     */
    public static final int TREE_CELL_GAP = 20;

    /**
     * The gap between the window's components
     */
    public static final int COMPONENT_GAP = 20;

    private TermView view;
    private JTree tree;

    private JLabel originJLabel;
    private JLabel subtermOriginsJLabel;

    private Services services;
    private PosInOccurrence termPio;
    private Sequent sequent;

    /**
     * Creates a new {@link OriginTermLabelWindow}.
     *
     * @param pos the position of the term whose origin shall be visualized.
     * @param node the node representing the proof state for which the term's origins shall be
     *  visualized.
     * @param services services.
     */
    public OriginTermLabelWindow(PosInOccurrence pos, Node node, Services services) {
        // TermView can only print sequents or formulas, not terms.
        if (pos != null) {
            while (!pos.subTerm().sort().equals(Sort.FORMULA)) {
                pos = pos.up();
            }
        }

        this.services = services;
        this.termPio = pos;
        this.sequent = node.sequent();

        JSplitPane contentPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
        setContentPane(contentPane);

        setSize(WIDTH, HEIGHT);
        setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
        setTitle("Term Origin");
        setIconImage(IconFactory.keyLogo());
        setLocationRelativeTo(null);
        setVisible(true);

        DefaultTreeModel treeModel = buildModel(pos);
        {
            tree = new JTree(treeModel);
            tree.setCellRenderer(new CellRenderer());
            ToolTipManager.sharedInstance().registerComponent(tree);

            tree.addTreeSelectionListener(e -> {
                TreeNode source = (TreeNode) tree.getLastSelectedPathComponent();

                if (source != null) {
                    ImmutableList<Integer> path = getPosTablePath(source.pos);

                    highlightInView(path);
                    updateJLabels(source.pos);
                }

                revalidate();
                repaint();
            });

            JScrollPane treeScrollPane = new JScrollPane(tree,
                    JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);

            treeScrollPane.setBorder(new TitledBorder(TREE_TITLE));

            treeScrollPane.setPreferredSize(new Dimension(WIDTH / 2, HEIGHT));
            add(treeScrollPane);

            treeScrollPane.addComponentListener(new ComponentAdapter() {

                @Override
                public void componentResized(ComponentEvent e) {
                    tree.setSize(treeScrollPane.getViewport().getSize());
                    tree.setUI(new BasicTreeUI());
                }
            });
        }

        {
            JSplitPane rightPanel = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
            JPanel bottomRightPanel = new JPanel(new GridLayout(1, 2, COMPONENT_GAP, COMPONENT_GAP));

            originJLabel = new JLabel();
            subtermOriginsJLabel = new JLabel();

            view = new TermView(pos, node, MainWindow.getInstance());
            view.setPreferredSize(new Dimension(WIDTH / 2, HEIGHT));

            view.addMouseListener(new MouseAdapter() {

                @Override
                public void mouseClicked(MouseEvent e) {
                    PosInSequent pis = view.getLastPosInSequent();

                    if (pis == null) {
                        return;
                    }

                    PosInOccurrence pos = pis.getPosInOccurrence();

                    if (pos == null) {
                        if (termPio != null) {
                            pos = new PosInOccurrence(
                                    termPio.sequentFormula(),
                                    termPio.posInTerm(),
                                    termPio.isInAntec());
                        }
                    } else {
                        if (termPio != null) {
                            PosInTerm completePos = termPio.posInTerm();

                            IntIterator it = pos.posInTerm().iterator();
                            while (it.hasNext()) {
                                completePos = completePos.down(it.next());
                            }

                            pos = new PosInOccurrence(
                                    termPio.sequentFormula(),
                                    completePos,
                                    termPio.isInAntec());
                        }
                    }

                    ImmutableList<Integer> path = getPosTablePath(pos);

                    highlightInView(path);
                    highlightInTree(getTreePath(path));
                    updateJLabels(pos);

                    revalidate();
                    repaint();
                }
            });

            JScrollPane viewScrollPane = new JScrollPane(view,
                    JScrollPane.VERTICAL_SCROLLBAR_ALWAYS,
                    JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            viewScrollPane.setBorder(new TitledBorder(VIEW_TITLE));
            rightPanel.add(viewScrollPane);

            view.printSequent();

            bottomRightPanel.add(originJLabel);
            JScrollPane subtermOriginsScrollPane = new JScrollPane(subtermOriginsJLabel,
                    JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
                    JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            bottomRightPanel.add(subtermOriginsScrollPane);
            bottomRightPanel.setBorder(new TitledBorder(ORIGIN_INFO_TITLE));
            originJLabel.setBorder(new TitledBorder(ORIGIN_TITLE));
            subtermOriginsScrollPane.setBorder(new TitledBorder(SUBTERM_ORIGINS_TITLE));

            originJLabel.setBackground(Color.WHITE);
            subtermOriginsJLabel.setBackground(Color.WHITE);

            rightPanel.add(bottomRightPanel);

            rightPanel.setDividerLocation(HEIGHT / 4 * 3);
            add(rightPanel);

            viewScrollPane.addComponentListener(new ComponentAdapter() {

                @Override
                public void componentResized(ComponentEvent e) {
                    view.printSequent();
                }
            });
        }

        contentPane.setDividerLocation(WIDTH / 2);
    }

    private DefaultTreeModel buildModel(PosInOccurrence pos) {
        TreeNode root = new TreeNode(pos);
        DefaultTreeModel result = new DefaultTreeModel(root);
        buildModel(root, pos, result);
        return result;
    }

    private void buildModel(
            TreeNode parentNode,
            PosInOccurrence parentPos,
            DefaultTreeModel treeModel) {
        if (parentPos == null) {
            int index = 0;

            ImmutableList<SequentFormula> children = sequent.antecedent().asList();

            for (SequentFormula child : children) {
                PosInOccurrence childPos = new PosInOccurrence(child, PosInTerm.getTopLevel(), true);
                TreeNode childNode = new TreeNode(childPos);

                treeModel.insertNodeInto(childNode, parentNode, index);
                buildModel(childNode, childPos, treeModel);

                ++index;
            }

            children = sequent.succedent().asList();

            for (SequentFormula child : children) {
                PosInOccurrence childPos = new PosInOccurrence(child, PosInTerm.getTopLevel(), false);
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

    private void highlightInView(ImmutableList<Integer> path) {
        view.removeHighlight(view.getColorHighlight(HIGHLIGHT_COLOR));
        view.printSequent();

        try {
            Range range = view.posTable.rangeForPath(path);
            range = new Range(range.start() + 1, range.end() + 1);

            view.paintHighlight(range, view.getColorHighlight(HIGHLIGHT_COLOR));
        } catch (ArrayIndexOutOfBoundsException e) {
            // The path does not point to a valid sub-term.
            // E.g., this can happen if pretty-printing is activated and the user selects
            // the subterm "#" of some number
            // (which only exists in the view when pretty-printing is deactivated.)
            // We simply ignore this error and do not paint any highlights.
        }
    }

    private void updateJLabels(PosInOccurrence pos) {
        originJLabel.setOpaque(false);
        subtermOriginsJLabel.setOpaque(false);

        if (pos == null) {
            originJLabel.setText("");

            subtermOriginsJLabel.setText("");

            return;
        }

        OriginTermLabel label = (OriginTermLabel) pos.subTerm().getLabel(OriginTermLabel.NAME);

        StringBuilder originText = new StringBuilder("<html>");
        StringBuilder subtermOriginsText = new StringBuilder("<html>");

        if (label != null) {
            // The term has an origin label. Show the term's origin.

            if (label.getOrigin().specType != SpecType.NONE) {
                originText.append(label.getOrigin());
                originJLabel.setOpaque(true);
            }

            for (Origin origin : label.getSubtermOrigins()) {
                subtermOriginsText.append(origin);
                subtermOriginsText.append("<br>");
                subtermOriginsJLabel.setOpaque(true);
            }

            if (label.getSubtermOrigins().isEmpty() && pos.subTerm().subs().size() != 0
                    && label.getOrigin().specType != SpecType.NONE) {
                subtermOriginsText.append(label.getOrigin());
                subtermOriginsJLabel.setOpaque(true);
            }
        } else {
            // The term has no origin label.
            // Iterate over its parent terms until we find one with an origin label,
            // then show that term's origin.

            final PosInOccurrence oldPos = pos;

            while (label == null && !pos.isTopLevel()) {
                pos = pos.up();
                label = (OriginTermLabel) pos.subTerm().getLabel(OriginTermLabel.NAME);
            }

            if (label != null && label.getOrigin().specType != SpecType.NONE) {
                originText.append(label.getOrigin());
                originJLabel.setOpaque(true);
            }

            if (label != null && oldPos.subTerm().subs().size() != 0
                    && label.getOrigin().specType != SpecType.NONE) {
                subtermOriginsText.append(label.getOrigin());
                subtermOriginsJLabel.setOpaque(true);
            }
        }

        originText.append("</html>");
        subtermOriginsText.append("</html>");

        originJLabel.setText(originText.toString());

        subtermOriginsJLabel.setText(subtermOriginsText.toString());
    }

    private ImmutableList<Integer> getPosTablePath(PosInOccurrence pos) {
        if (pos == null) {
            return ImmutableSLList.<Integer>nil().prepend(0);
        }

        InitialPositionTable posTable = view.posTable;

        ImmutableList<Integer> path = posTable.pathForPosition(pos, view.getFilter());

        if (termPio != null) {
            ImmutableList<Integer> prefixPath = posTable.pathForPosition(
                    termPio, view.getFilter());

            final int n = prefixPath.size();

            for (int i = 0; i < n; ++i) {
                assert path.head() == prefixPath.head();

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

    private class CellRenderer extends DefaultTreeCellRenderer {

        private static final long serialVersionUID = -7479404026154193661L;

        @Override
        public Component getTreeCellRendererComponent(
                JTree tree, Object value,
                boolean selected, boolean expanded,
                boolean leaf, int row, boolean hasFocus) {
            TreeNode node = (TreeNode) value;
            Term term = node.term;
            BasicTreeUI ui = (BasicTreeUI) tree.getUI();

            JLabel termTextLabel = (JLabel) super.getTreeCellRendererComponent(
                    tree, value, selected, expanded,
                    leaf, row, hasFocus);
            termTextLabel.setText(getShortTermText(term));
            termTextLabel.setBackground(OriginTermLabelWindow.this.getBackground());

            JLabel originTextLabel = new JLabel();
            OriginTermLabel originLabel = term == null
                    ? null
                    : (OriginTermLabel) term.getLabel(OriginTermLabel.NAME);

            if (originLabel != null) {
                originTextLabel.setText(getShortOriginText(originLabel.getOrigin()));
                originTextLabel.setHorizontalAlignment(SwingConstants.TRAILING);
            }

            JPanel result = new JPanel(new BorderLayout(TREE_CELL_GAP, TREE_CELL_GAP));

            final int indent =
                    (ui.getLeftChildIndent() + ui.getRightChildIndent()) * node.getLevel();

            result.setPreferredSize(new Dimension(
                    tree.getWidth() - indent,
                    super.getPreferredSize().height));

            result.add(termTextLabel, BorderLayout.LINE_START);
            result.add(originTextLabel, BorderLayout.LINE_END);

            result.setBorder(BorderFactory.createLineBorder(Color.BLACK));
            result.setBackground(Color.WHITE);

            if (originLabel != null) {
                result.setToolTipText(getFullText(term, originLabel.getOrigin()));
            }

            return result;
        }

        private String getShortOriginText(Origin origin) {
            return origin.specType.toString();
        }

        private String getFullText(Term term, Origin origin) {
            String text;

            if (term == null) {
                text = LogicPrinter.quickPrintSequent(sequent, services);
            } else {
                text = LogicPrinter.quickPrintTerm(term, services);
            }

            return "<html><b>" + origin + "</b><hr>"
                + text
                    .replace("&", "&amp;")
                    .replace("<", "&lt;")
                    .replace(">", "&gt;")
                    .replace(" ", "&nbsp;")
                    .replace("\t", "&nbsp;&nbsp;&nbsp;&nbsp;")
                    .replace("\n", "<br>")
                + "</html>";
        }

        private String getShortTermText(Term term) {
            String text;

            if (term == null) {
                text = LogicPrinter.quickPrintSequent(sequent, services);
            } else {
                text = LogicPrinter.quickPrintTerm(term, services);
            }

            int endIndex = text.indexOf("\n");

            if (endIndex != text.length() - 1) {
                return text.replaceAll("\\s+", " ") + " ...";
            } else {
                return text.substring(0, text.indexOf("\n")).replaceAll("\\s+", " ");
            }
        }
    }

    private class TreeNode extends DefaultMutableTreeNode {

        private static final long serialVersionUID = 8257931535327190600L;

        private PosInOccurrence pos;
        private Term term;

        private TreeNode(PosInOccurrence pos) {
            super(pos);
            this.pos = pos;

            if (pos != null) {
                this.term = pos.subTerm();
            }
        }
    }

    private class TermView extends SequentView {

        private static final long serialVersionUID = 2048113301808983374L;

        private InitialPositionTable posTable = new InitialPositionTable();
        private Node node;

        TermView(PosInOccurrence pos, Node node, MainWindow mainWindow) {
            super(mainWindow);
            this.node = node;

            final NotationInfo ni = new NotationInfo();
            if (services != null) {
                ni.refresh(services,
                        NotationInfo.DEFAULT_PRETTY_SYNTAX, NotationInfo.DEFAULT_UNICODE_ENABLED);
            }

            setLogicPrinter(new SequentViewLogicPrinter(
                    new ProgramPrinter(), ni, services, new TermLabelVisibilityManager()) {

                @Override
                public void printSequent(SequentPrintFilter filter,
                        boolean finalbreak) {
                    try {
                        ImmutableList<SequentPrintFilterEntry> antec = filter.getFilteredAntec();
                        ImmutableList<SequentPrintFilterEntry> succ  = filter.getFilteredSucc();
                        markStartSub();
                        startTerm(antec.size()+succ.size());
                        layouter.beginC(1).ind();
                        printSemisequent(antec);

                        if (pos == null) {
                            layouter.brk(1,-1).print("==>").brk(1);
                        }

                        printSemisequent(succ);
                        if (finalbreak) {
                            layouter.brk(0);
                        }
                        markEndSub();
                        layouter.end();
                    } catch (IOException e) {
                        throw new RuntimeException (
                                "IO Exception in pretty printer:\n"+e);
                    } catch (UnbalancedBlocksException e) {
                        throw new RuntimeException (
                                "Unbalanced blocks in pretty printer:\n"+e);
                    }
                }
            });

            if (pos != null) {
                setFilter(new ShowSelectedSequentPrintFilter(pos));
            } else {
                setFilter(new IdentitySequentPrintFilter());
            }
        }

        @Override
        public SequentPrintFilter getFilter() {
            return super.getFilter();
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
            getLogicPrinter().update(getFilter(), computeLineWidth());
            setText(getSyntaxHighlighter().process(getLogicPrinter().toString(), node));
            posTable = getLogicPrinter().getInitialPositionTable();

            updateHidingProperty();
        }
    }
}
