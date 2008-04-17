// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.*;
import java.util.ArrayList;

import javax.swing.*;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.event.TreeModelListener;
import javax.swing.table.AbstractTableModel;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.TreeCellRenderer;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreePath;

import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.visualization.*;

/*
 * Created on 24.06.2005
 */

public class ProofVisTreeView extends JFrame implements java.io.Serializable {

    private JPanel jContentPane = null;

    private JScrollPane jScrollPane = null;

    private JTree jTree = null; 

    private JButton jButton = null;

    private JCheckBox jCheckBox = null;

    private JTable table;

    private ExecutionTraceModel[] traces, filterTraces;
    
    ExecutionTraceModel selection=null;

    public ProofVisTreeView(VisualizationModel visModel) {
        this.traces = visModel.getExecutionTraces();
        this.filterTraces = visModel.getInterestingExecutionTraces();
        if (traces != null && traces.length>0) {
            selection = traces[0];
        }
        
        setContentPane(getJContentPane());
        setSize(425, 570);
        setTitle("Visualization of Node " + visModel.getNode().serialNr());
        setVisible(true);
        toFront();
    }


    private String removeLineBreaks(String s) {
        return s.replaceAll("\n"," ");
    }

    /**
     * This method initializes jContentPane
     * 
     * @return javax.swing.JPanel
     */
    private JPanel getJContentPane() {
        if (jContentPane == null) {
            jContentPane = new JPanel();
            jContentPane.setLayout(new FlowLayout());
            jContentPane.add(getJScrollPane());
            jContentPane.add(getSelectionPane());
            jContentPane.add(getButtonPanel());
            pack();
        }

        return jContentPane;
    }

    /**
     * This method initializes jScrollPane
     * 
     * @return javax.swing.JScrollPane
     */
    private JScrollPane getJScrollPane() {
        if (jScrollPane == null) {

            jScrollPane = new JScrollPane(getJTree(),
                    ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
                    ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            jScrollPane.setMinimumSize(new java.awt.Dimension(390, 400));
            jScrollPane.setPreferredSize(new java.awt.Dimension(390, 400));
        }
        return jScrollPane;
    }

    /**
     * This method initializes jTree
     * 
     * @return javax.swing.JTree
     */
    private JTree getJTree() {
        if (jTree == null) {
            jTree = new JTree(new Object[0]);
            ContextTraceElement cte=null;
            if (selection!=null){
                cte = selection.getFirstContextTraceElement();
                jTree.setModel(new PVTreeModel(cte));
                jTree.setCellRenderer(new CellRenderer());
            }
            jTree.setRootVisible(false);
            ToolTipManager.sharedInstance().registerComponent(jTree);
            MouseListener ml = new MouseAdapter() {
                public void mousePressed(MouseEvent e) {
                    if (e.isPopupTrigger()) {
                        TreePath selPath = jTree.getPathForLocation
                            (e.getX(), e.getY());
                        if (selPath!=null) {
                            JPopupMenu popup = new TreePopupMenu
                                (selPath.getLastPathComponent());
                            popup.show(e.getComponent(),
                                       e.getX(), e.getY());
                        }
                    }
                }
            };
            jTree.addMouseListener(ml);
            if (cte!=null && cte!=TraceElement.END)
                jTree.makeVisible(getPath());
        }
        return jTree;
    }
    
    
    public TreePath getPath() {

        ContextTraceElement[] path = selection.getPath(selection
                .getLastContextTraceElement());
        ContextTraceElement[] pathResult = new ContextTraceElement[1 + path.length];
        pathResult[0] = (ContextTraceElement) jTree.getModel().getRoot();
        for (int i = 0; i < path.length; i++) {
            pathResult[i + 1] = path[i];

        }

        return new TreePath(pathResult);
    }

    /**
     * This method initializes the button panel
     * 
     * @return javax.swing.JButton
     */
    private JPanel getButtonPanel() {
        JPanel buttonPanel = new JPanel();
        if (jButton == null) {
            jButton = new JButton();
            jButton.setText("OK");
            jButton.setPreferredSize(new java.awt.Dimension(75, 35));
        }
        ActionListener okListener = new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setVisible(false);
                dispose();
            }
        };
        jButton.addActionListener(okListener);

        if (jCheckBox == null) {
            jCheckBox = new JCheckBox();
            jCheckBox.setText("Filter uninteresting traces");
        }
        ItemListener itemListener = new ItemListener() {
            public void itemStateChanged(ItemEvent e) {
                Object source = e.getItemSelectable();
                if (source == jCheckBox) {
                    if (e.getStateChange() == ItemEvent.SELECTED) {
                        ((TracesTableModel) table.getModel()).setTraces(filterTraces);

                    } else {
                        ((TracesTableModel) table.getModel())
                                .setTraces(traces);
                    }
                    table.repaint();
                    table.doLayout();
                }
            }
        };
        jButton.addActionListener(okListener);
        jCheckBox.addItemListener(itemListener);
        buttonPanel.add(jButton);
        buttonPanel.add(jCheckBox);
        return buttonPanel;
    }

    public JScrollPane getSelectionPane() {
        if (traces!=null)
            table = new JTable(new TracesTableModel(traces));
        else table = new JTable(0,0);

        table.setPreferredScrollableViewportSize(new Dimension(390, 70));

        table.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        
        ListSelectionModel rowSM = table.getSelectionModel();
        if (selection!=null)
            table.addRowSelectionInterval(0,0);
        rowSM.addListSelectionListener(new ListSelectionListener() {
            public void valueChanged(ListSelectionEvent e) {
                // Ignore extra messages.
                if (e.getValueIsAdjusting())
                    return;
                ListSelectionModel lsm = (ListSelectionModel) e.getSource();
                if (lsm.isSelectionEmpty()) {
                } else {
                    int selectedRow = lsm.getMinSelectionIndex();
                    selection = ((TracesTableModel) table.getModel())
                            .getTrace(selectedRow);
                    ContextTraceElement cte = selection.getFirstContextTraceElement();
                    jTree.setModel(new PVTreeModel(cte));
                    if (cte!=TraceElement.END)
                        jTree.makeVisible(getPath());
                    jTree.updateUI();
                }
            }
        });
        table.setColumnSelectionAllowed(false);
        // Create the scroll pane and add the table to it.
        JScrollPane scrollPane = new JScrollPane(table);
        scrollPane.setPreferredSize(new Dimension(390, 70));
        scrollPane.setMinimumSize(new Dimension(390, 70));
        // Add the scroll pane to this panel.
        return (scrollPane);

    }

    class PVTreeModel implements TreeModel {

        ParentContextTraceElement root = new ParentContextTraceElement();

        Object[] children;

        public PVTreeModel(ContextTraceElement ste) {
            root = new ParentContextTraceElement();
            ArrayList<ContextTraceElement> childr = new ArrayList<ContextTraceElement>();
            ContextTraceElement cte = ste;
            while ((cte != TraceElement.END)
                    && (TraceElement.PARENTROOT == cte.getParent())) {
                childr.add(cte);
                if (cte instanceof ParentContextTraceElement)
                    cte = ((ParentContextTraceElement) cte).stepOver();
                else
                    cte = cte.getNextExecuted();
            }
            children = childr.toArray();
        }

        public void addTreeModelListener(TreeModelListener l) {
        }

        public Object getChild(Object parent, int index) {
            if (parent == root) {
                return children[index];
            } else
                return ((ParentContextTraceElement) parent).getChildren()[index];
        }

        public int getChildCount(Object parent) {
            if (parent == root)
                return children.length;
            else
                return ((ParentContextTraceElement) parent).getChildren().length;
        }

        public int getIndexOfChild(Object parent, Object child) {
            if ((parent == null) || (child == null))
                return -1;
            Object[] ch = ((ParentContextTraceElement) parent).getChildren();
            for (int i = 0; i < ch.length; i++) {
                if (ch[i].equals(child))
                    return i;
            }
            return -1;
        }

        public Object getRoot() {
            return root;
        }

        public boolean isLeaf(Object node) {
            if (node == root)
                return false;
            if (!(node instanceof ParentContextTraceElement))
                return true;
            if (((ParentContextTraceElement) node).getChildren().length == 0)
                return true;
            return false;

        }

        public void removeTreeModelListener(TreeModelListener l) {
        }

        public void valueForPathChanged(TreePath path, Object newValue) {
        }
        
    }

    class CellRenderer extends DefaultTreeCellRenderer implements
            TreeCellRenderer, java.io.Serializable {

        public Component getTreeCellRendererComponent(JTree list, Object value,
                boolean selected, boolean expanded, boolean leaf, int row,
                boolean hasFocus) {
            String s;
            ContextTraceElement cte = null;
            if (value != null) {
                cte = (ContextTraceElement) value;
                if (cte.getContextStatement() != null) {
                    s = ""+ cte.getContextStatement();
                } else {
                    s = "" + cte.getSrcElement();
                }


                int i = s.indexOf("\n");
                if (i > -1) {
                    s = s.substring(0, i);
                }
            } else {
                s = "NULL";
            }
            DefaultTreeCellRenderer tree_cell = (DefaultTreeCellRenderer) super
                    .getTreeCellRendererComponent(list, s, selected, expanded,
                            leaf, row, hasFocus);

            tree_cell.setBackground(Color.WHITE);
            tree_cell.setBackgroundNonSelectionColor(Color.WHITE);
            tree_cell.setBackgroundSelectionColor(Color.WHITE);
            
            tree_cell.setFont(list.getFont());
            tree_cell.setText(s);
           
            
            if (cte != null) {
                String toolTipText = "<html><b>Node "+cte.serialNr()+"</b>";
                if (cte.getLabel()!=null 
                        && (cte.getLabel().length()>0)){
                    toolTipText += "<br><b>"+cte.getLabel()+"</b>";
                }
                if (cte!=TraceElement.PARENTROOT && cte.getParent()!=null &&
                        (cte.getParent()!=TraceElement.PARENTROOT)&& 
                        (cte.getParent().getSrcElement() instanceof LoopStatement)){
                    toolTipText += "<br><b>Unwound:</b> "+cte.getNumberOfExecutions()+ " time";
                    if (cte.getNumberOfExecutions()>1) toolTipText+="s";
                }
                if ((cte==selection.getLastContextTraceElement())&&
                        selection.uncaughtException()){                
                     tree_cell.setBackground(Color.PINK);
                     tree_cell.setBackgroundNonSelectionColor(Color.PINK);
                     tree_cell.setBackgroundSelectionColor(Color.PINK);
                     toolTipText+="<br><b>Uncaught Exception: </b>"+removeLineBreaks(""+selection.getUncaughtException().getSrcElement());
                 }
                 toolTipText+="</html>";
                 tree_cell.setToolTipText(toolTipText);
            }           
            tree_cell.setLeafIcon(null);
            return tree_cell;
        }

    }

    class TracesTableModel extends AbstractTableModel {
        String[] columnNames = { "Java Program", "First Node", "Last Node" };

        ExecutionTraceModel[] traces;

        public TracesTableModel(ExecutionTraceModel[] traces) {
            super();
            this.traces = traces;

        }

        public int getColumnCount() {
            return columnNames.length;
        }

        public int getRowCount() {
            return traces.length;
        }

        public String getColumnName(int col) {
            return columnNames[col];
        }

        public Object getValueAt(int row, int col) {
            if (col == 0)
                return removeLineBreaks(""
                        + traces[row].getFirstTraceElement().getProgram());
            else if (col == 1)
                return "" + traces[row].getFirstNode().serialNr();
            else
                return "" + traces[row].getLastNode().serialNr();
        }

        public Class<? extends Object> getColumnClass(int c) {
            return getValueAt(0, c).getClass();
        }

        public boolean isCellEditable(int row, int col) {
            return false;
        }

        public ExecutionTraceModel getTrace(int row) {
            return traces[row];
        }

        public void setTraces(ExecutionTraceModel[] traces) {
            this.traces = traces;
            fireTableDataChanged();
        }

    }
    
    
    
    class TreePopupMenu extends JPopupMenu 
        implements ActionListener {     
        
        private JMenuItem showNode   = new JMenuItem("Show Node");
        private ContextTraceElement cte;

        public TreePopupMenu(Object node) {
            super("Choose Action");
            if (node instanceof ContextTraceElement){
                cte = (ContextTraceElement) node;
                create();
            }
        }

        private void create() {     
            this.add(showNode);
            showNode.addActionListener(this);
        }

        public void actionPerformed(ActionEvent e) {
            if (e.getSource() == showNode) {
                Main.getInstance().mediator().getSelectionModel().setSelectedNode(cte.node());
	    } 	    
	}
    }





}
