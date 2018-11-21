package de.uka.ilkd.key.gui.proofExploration;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.IOException;

import javax.swing.BorderFactory;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTree;
import javax.swing.SwingConstants;
import javax.swing.plaf.basic.BasicTreeUI;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.IntIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.pp.SequentPrintFilterEntry;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.ShowSelectedSequentPrintFilter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.pp.UnbalancedBlocksException;

/**
 * This window visualizes the {@link OriginTermLabel}s of a term and its sub-terms.
 *
 * @author lanzinger
 */
public class OriginTermLabelWindow extends JFrame {

    private static final long serialVersionUID = -2791483814174192622L;

    public static final int WIDTH = 1280;
    public static final int HEIGHT = 720;
    public static final boolean PRINT_LINE_BREAKS_IN_TREE_NODES = true;
    public static final Color HIGHLIGHT_COLOR = Color.ORANGE;
    public static final String ORIGIN_HEADER = "Origin of term";
    public static final String SUBTERM_ORIGINS_HEADER = "Origins of (former) subterms";

    /**
     * The gap between a term and its origin in the tree view.
     */
    public static final int TREE_CELL_GAP = 20;

    /**
     * The gap between the window's components
     */
    public static final int COMPONENT_GAP = 20;

    protected TermView view;
    protected JTree tree;

    protected JLabel originJLabel;
    protected JLabel subtermOriginsJLabel;

    protected Services services;
    protected PosInOccurrence termPio;
    protected Sequent sequent;

    public OriginTermLabelWindow(PosInOccurrence pos, Node node, Services services) {
        this.services = services;
        this.termPio = pos;
        this.sequent = node.sequent();

        setLayout(new GridLayout(1, 2, COMPONENT_GAP, COMPONENT_GAP));
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
            tree.addTreeSelectionListener(e -> {
                TreeNode source = (TreeNode) tree.getLastSelectedPathComponent();

                ImmutableList<Integer> path = getPosTablePath(source.pos);

                highlightInView(path);
                updateJLabels(source.pos);
            });

            JScrollPane treeScrollPane = new JScrollPane(tree,
                    JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);

            treeScrollPane.setPreferredSize(new Dimension(WIDTH / 2, HEIGHT));
            add(treeScrollPane);
        }

        {
            JPanel rightPanel = new JPanel(new GridLayout(2, 1, COMPONENT_GAP, COMPONENT_GAP));
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
                }
            });

            rightPanel.add(view);

            view.printSequent();

            bottomRightPanel.add(originJLabel);
            bottomRightPanel.add(subtermOriginsJLabel);
            rightPanel.add(bottomRightPanel);

            add(rightPanel);
        }

        addComponentListener(new ComponentAdapter() {

            @Override
            public void componentResized(ComponentEvent e) {
                tree.setUI(new BasicTreeUI());
                view.printSequent();
            }
        });
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

        Range range = view.posTable.rangeForPath(path);
        range = new Range(range.start() + 1, range.end() + 1);

        view.paintHighlight(range, view.getColorHighlight(HIGHLIGHT_COLOR));
    }

    private void updateJLabels(PosInOccurrence pos) {
        if (pos == null) {
            originJLabel.setText("<html>" + "<b>" + ORIGIN_HEADER + ":</b><br></html>");
            subtermOriginsJLabel.setText(
                    "<html>" + "<b>" + SUBTERM_ORIGINS_HEADER + ":</b><br></html>");
            return;
        }

        OriginTermLabel label = (OriginTermLabel) pos.subTerm().getLabel(OriginTermLabel.NAME);

        StringBuilder originText = new StringBuilder(
                "<html>" + "<b>" + ORIGIN_HEADER + ":</b><br>");

        StringBuilder subtermOriginsText = new StringBuilder(
                "<html>" + "<b>" + SUBTERM_ORIGINS_HEADER + ":</b><br>");

        if (label != null) {
            originText.append(label.getOrigin());

            for (Origin origin : label.getSubtermOrigins()) {
                subtermOriginsText.append(origin);
                subtermOriginsText.append("<br>");
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

    private String getTermText(Term term) {
        String text;

        if (term == null) {
            text = LogicPrinter.quickPrintSequent(sequent, services);
        } else {
            text = LogicPrinter.quickPrintTerm(term, services);
        }

        if (PRINT_LINE_BREAKS_IN_TREE_NODES) {
            return "<html>"
                    + text
                        .replace("&", "&amp;")
                        .replace("<", "&lt;")
                        .replace(">", "&gt;")
                        .replace(" ", "&nbsp;")
                        .replace("\t", "&nbsp;&nbsp;&nbsp;&nbsp;")
                        .replace("\n", "<br>")
                    + "</html>";
        } else {
            return text.replaceAll("\\s+", " ");
        }
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
            termTextLabel.setText(getTermText(term));
            termTextLabel.setBackground(OriginTermLabelWindow.this.getBackground());

            JLabel originTextLabel = new JLabel();
            TermLabel originLabel = term == null ? null : term.getLabel(OriginTermLabel.NAME);

            if (originLabel != null) {
                originTextLabel.setText(originLabel.getChild(0).toString());
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
            return result;
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

        private InitialPositionTable posTable;
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
