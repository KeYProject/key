package de.uka.ilkd.key.gui.proofExploration;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.GridLayout;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.io.IOException;

import javax.swing.BorderFactory;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTree;
import javax.swing.SwingConstants;
import javax.swing.SwingUtilities;
import javax.swing.plaf.basic.BasicTreeUI;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.DefaultTreeModel;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.InnerNodeView;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.ShowSelectedSequentPrintFilter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

/**
 * This window visualizes the {@link OriginTermLabel}s of a term and its children.
 *
 * @author lanzinger
 */
public class OriginTermLabelWindow extends JFrame {

    private static final long serialVersionUID = -2791483814174192622L;

    public static final int WIDTH = 1280;
    public static final int HEIGHT = 720;

    public static final boolean PRINT_LINE_BREAKS_IN_TREE_NODES = true;
    
    public static final Dimension INITIAL_COMPONENT_SIZE = new Dimension(WIDTH / 2, HEIGHT);
    
    public static final Color HIGHLIGHT_COLOR = Color.ORANGE;
    
    private View view;
    private JTree tree;

    /**
     * The gap between a term and its origin in the tree view.
     */
    public static final int TREE_CELL_GAP = 20;
    
    /**
     * The gap between the {@link JTree} and the {@link View}
     */
    public static final int COMPONENT_GAP = 20;

    private Services services;

    public OriginTermLabelWindow(PosInOccurrence pos, Node node, Services services) {
        this.services = services;
        Term term = pos.subTerm();
        
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
                selectionChanged(source.pos);
            });

            JScrollPane treeScrollPane = new JScrollPane(tree,
                    JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);

            treeScrollPane.setPreferredSize(INITIAL_COMPONENT_SIZE);
            add(treeScrollPane);
        }

        {
            view = new View(pos, node, MainWindow.getInstance());
            view.setPreferredSize(INITIAL_COMPONENT_SIZE);
            add(view);
            view.printSequent();
        }

        addComponentListener(new ComponentAdapter() {

            @Override
            public void componentResized(ComponentEvent e) {                
                tree.setUI(new BasicTreeUI());
                view.printSequent();
            }
        });

        selectionChanged(pos);
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
        ImmutableArray<Term> children = parentPos.subTerm().subs();

        for (int i = 0; i < children.size(); ++i) {
            TreeNode childNode = new TreeNode(parentPos.down(i));

            treeModel.insertNodeInto(childNode, parentNode, i);
            buildModel(childNode, parentPos.down(i), treeModel);
        }
    }

    private void selectionChanged(PosInOccurrence pos) {
        //view.removeHighlight(view.getColorHighlight(HIGHLIGHT_COLOR));
        
        InitialPositionTable posTable = view.posTable;
        

        
        posTable.pathForPosition(pos, view.getFilter()).stream().forEach(i -> System.out.println(i + ", "));
        
        Range range = posTable.rangeForPath(posTable.pathForPosition(pos, view.getFilter()));

        view.paintHighlight(range, view.getColorHighlight(HIGHLIGHT_COLOR));
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
            TermLabel originLabel = term.getLabel(OriginTermLabel.NAME);

            if (originLabel != null) {
                originTextLabel.setText(getOriginText((Origin) originLabel.getChild(0)));
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

        private String getOriginText(Origin origin) {
            String line = origin.line == -1 ? "" : " (line " + origin.line + ")";
            return origin.specType + ", " + origin.fileName + line;
        }

        private String getTermText(Term term) {
            if (PRINT_LINE_BREAKS_IN_TREE_NODES) {
                return "<html>"
                        + LogicPrinter.quickPrintTerm(term, services)
                            .replace("&", "&amp;")
                            .replace("<", "&lt;")
                            .replace(">", "&gt;")
                            .replace(" ", "&nbsp;")
                            .replace("\t", "&nbsp;&nbsp;&nbsp;&nbsp;")
                            .replace("\n", "<br>")
                        + "</html>";
            } else {
                return LogicPrinter.quickPrintTerm(term, services).replaceAll("\\s+", " ");
            }
        }
    }

    private class TreeNode extends DefaultMutableTreeNode {

        private static final long serialVersionUID = 8257931535327190600L;

        private PosInOccurrence pos;
        private Term term;

        private TreeNode(PosInOccurrence pos) {
            super(pos.subTerm());
            this.pos = pos;
            this.term = pos.subTerm();
        }
    }
    
    private class View extends SequentView {
        
        private static final long serialVersionUID = 2048113301808983374L;
        
        private InitialPositionTable posTable;
        private Term term;
        private PosInOccurrence pos;
        private Node node;

        View(PosInOccurrence pos, Node node, MainWindow mainWindow) {
            super(mainWindow);
            this.term = pos.subTerm();
            this.pos = pos;
            this.node = node;
            
            final NotationInfo ni = new NotationInfo();
            if (services != null) {
                ni.refresh(services,
                        NotationInfo.DEFAULT_PRETTY_SYNTAX, NotationInfo.DEFAULT_UNICODE_ENABLED);
            }
            
            setLogicPrinter(new SequentViewLogicPrinter(
                    new ProgramPrinter(), ni, services, new TermLabelVisibilityManager()));
            
            setFilter0(new ShowSelectedSequentPrintFilter(pos));
        }
        
        // This is very ugly, but it prevents any filters from the main window's search bar being
        // applied to this view.
        
        @Override
        public void setFilter(SequentPrintFilter sequentPrintFilter) { }
        
        private void setFilter0(ShowSelectedSequentPrintFilter sequentPrintFilter) {
            super.setFilter(sequentPrintFilter);
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
        public final synchronized void printSequent() {
            getLogicPrinter().update(getFilter(), computeLineWidth());
            System.out.println(getLogicPrinter().result());
            setText(getSyntaxHighlighter().process(getLogicPrinter().result().toString(), node));
            posTable = getLogicPrinter().getInitialPositionTable();

            updateHidingProperty();
        }
    }
}
