package de.uka.ilkd.key.gui.proofExploration;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.util.SortedSet;
import java.util.StringJoiner;
import java.util.TreeSet;

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

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.pp.LogicPrinter;

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

    /**
     * The gap between a term and its origin in the tree view.
     */
    public static final int TREE_CELL_GAP = 20;

    private JLabel childrenOriginsLabel;
    private JLabel originLabel;
    private Services services;
    private SortedSet<Origin> allOrigins = new TreeSet<>();

    public OriginTermLabelWindow(Term term, Services services) {
        this.services = services;
        setLayout(new BorderLayout());
        setSize(WIDTH, HEIGHT);
        setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
        setTitle("Term Origin");
        setIconImage(IconFactory.keyLogo());
        setLocationRelativeTo(null);
        setVisible(true);

        DefaultTreeModel treeModel = buildModel(term);
        JTree tree = new JTree(treeModel);
        {
            tree.setCellRenderer(new CellRenderer());
            tree.addTreeSelectionListener(e -> {
                Node source = (Node) tree.getLastSelectedPathComponent();
                selectionChanged(source.term);
            });

            JScrollPane treeScrollPane = new JScrollPane(tree,
                    JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);

            add(treeScrollPane, BorderLayout.LINE_START);
        }

        //TODO add SequentView at BorderLayout.LINE_END

        addComponentListener(new ComponentAdapter() {

            @Override
            public void componentResized(ComponentEvent e) {
                // resize tree nodes
                tree.setUI(new BasicTreeUI());
            }
        });

        selectionChanged(term);
    }

    private DefaultTreeModel buildModel(Term term) {
        Node root = new Node(term);
        DefaultTreeModel result = new DefaultTreeModel(root);
        buildModel(root, term, result);
        return result;
    }

    private void buildModel(Node parentNode, Term parentTerm, DefaultTreeModel treeModel) {
        ImmutableArray<Term> children = parentTerm.subs();

        for (int i = 0; i < children.size(); ++i) {
            Term childTerm = children.get(i);
            Node childNode = new Node(childTerm);

            treeModel.insertNodeInto(childNode, parentNode, i);

            Origin origin = getOrigin(childTerm);
            if (origin != null) {
                allOrigins.add(origin);
            }

            buildModel(childNode, childTerm, treeModel);
        }
    }

    private void collectChildOrigins(Term term) {
        Origin origin = getOrigin(term);
        if (origin != null) {
            allOrigins.add(origin);
        }

        ImmutableArray<Term> children = term.subs();

        for (int i = 0; i < children.size(); ++i) {
            Term childTerm = children.get(i);
            collectChildOrigins(childTerm);
        }
    }

    private void selectionChanged(Term selectedTerm) {
        allOrigins.clear();
        collectChildOrigins(selectedTerm);

        StringJoiner allOriginsStr = new StringJoiner("<br>", "<html>", "</html>");

        for (Origin origin : allOrigins) {
            allOriginsStr.add(origin.toString());
        }

        childrenOriginsLabel.setText(allOriginsStr.toString());

        originLabel.setText(getOriginAsString(selectedTerm));
    }

    private Origin getOrigin(Term term) {
        TermLabel label = term.getLabel(OriginTermLabel.NAME);

        if (label == null) {
            return null;
        } else {
            return (Origin) label.getChild(0);
        }
    }

    private String getOriginAsString(Term term) {
        Origin origin = getOrigin(term);
        return origin == null ? "" : origin.toString();
    }

    private class CellRenderer extends DefaultTreeCellRenderer {

        private static final long serialVersionUID = -7479404026154193661L;

        @Override
        public Component getTreeCellRendererComponent(
                JTree tree, Object value,
                boolean selected, boolean expanded,
                boolean leaf, int row, boolean hasFocus) {
            Node node = (Node) value;
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
                    OriginTermLabelWindow.this.getWidth() - indent,
                    super.getPreferredSize().height));

            result.add(termTextLabel, BorderLayout.LINE_START);
            result.add(originTextLabel, BorderLayout.LINE_END);

            result.setBorder(BorderFactory.createLineBorder(Color.BLACK));
            return result;
        }

        private String getOriginText(Origin origin) {
            String line = origin.line == -1 ? "" : " (line " + origin.line + ")";

            if (PRINT_LINE_BREAKS_IN_TREE_NODES) {
                return "<html>"
                        + origin.specType + "<br>"
                        + origin.fileName + line
                        + "</html>";
            } else {
                return origin.specType + ", " + origin.fileName + line;
            }
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

    private class Node extends DefaultMutableTreeNode {

        private static final long serialVersionUID = 8257931535327190600L;

        private Term term;

        private Node(Term term) {
            super(term);
            this.term = term;
        }
    }
}
