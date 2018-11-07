package de.uka.ilkd.key.gui.proofExploration;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Font;
import java.util.SortedSet;
import java.util.StringJoiner;
import java.util.TreeSet;

import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTree;
import javax.swing.SwingConstants;
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

    public static final int HEADING_FONT_SIZE = 16;
    public static final int GAP_BELOW_HEADING = 20;

    private JLabel childrenOriginsLabel;
    private JLabel originLabel;
    private Services services;
    private SortedSet<Origin> allOrigins = new TreeSet<>();

    public OriginTermLabelWindow(Term term, Services services) {
        this.services = services;

        DefaultTreeModel treeModel = buildModel(term);
        setLayout(new BorderLayout());
        {
            JTree tree = new JTree(treeModel);
            tree.setCellRenderer(new CellRenderer());
            tree.addTreeSelectionListener(e -> {
                Node source = (Node) tree.getLastSelectedPathComponent();
                selectionChanged(source.term);
            });

            JScrollPane treeScrollPane = new JScrollPane(tree,
                    JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_ALWAYS);

            add(treeScrollPane, BorderLayout.CENTER);
        }

        {
            JPanel topPanel = new JPanel(new BorderLayout());

            {
                JPanel topLeftPanel = new JPanel(new BorderLayout(0, GAP_BELOW_HEADING));

                originLabel = new JLabel();

                JLabel originTitle = new JLabel("Origin of selected term", SwingConstants.CENTER);
                originTitle.setFont(originTitle.getFont().deriveFont(
                        Font.BOLD, HEADING_FONT_SIZE));
                topLeftPanel.add(originTitle, BorderLayout.PAGE_START);

                originLabel.setPreferredSize(new Dimension(WIDTH / 2, 100));
                topLeftPanel.add(originLabel, BorderLayout.CENTER);

                topPanel.add(topLeftPanel, BorderLayout.LINE_START);
            }

            {
                JPanel topRightPanel = new JPanel(new BorderLayout(0, GAP_BELOW_HEADING));

                childrenOriginsLabel = new JLabel();

                JLabel childrenOriginsTitle = new JLabel("Origins of child terms", SwingConstants.CENTER);
                childrenOriginsTitle.setFont(childrenOriginsTitle.getFont().deriveFont(
                        Font.BOLD, HEADING_FONT_SIZE));
                topRightPanel.add(childrenOriginsTitle, BorderLayout.PAGE_START);

                JScrollPane childrenOriginsScrollPane = new JScrollPane(childrenOriginsLabel,
                        JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);

                childrenOriginsScrollPane.setPreferredSize(new Dimension(WIDTH / 2, 100));
                topRightPanel.add(childrenOriginsScrollPane, BorderLayout.CENTER);

                topPanel.add(topRightPanel, BorderLayout.LINE_END);
            }

            topPanel.setPreferredSize(new Dimension(WIDTH, 100));
            add(topPanel, BorderLayout.PAGE_START);
        }

        setSize(WIDTH, HEIGHT);
        setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
        setTitle("Term Origin");
        setIconImage(IconFactory.keyLogo());
        setLocationRelativeTo(null);
        setVisible(true);

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
            JLabel label = (JLabel) super.getTreeCellRendererComponent(
                    tree, value, selected, expanded,
                    leaf, row, hasFocus);
            Node node = (Node) value;

            label.setText(LogicPrinter.quickPrintTerm(node.term, services));

            return label;
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
