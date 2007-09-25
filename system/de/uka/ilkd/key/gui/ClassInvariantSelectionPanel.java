// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;


import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.*;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.Debug;


/**
 * A dialog for selecting class invariants.
 */
public class ClassInvariantSelectionPanel extends JPanel {
    
    private Set modelClasses;
    private boolean useThroughoutInvs;
    
    private ListOfClassInvariant selectedInvs 
            = SLListOfClassInvariant.EMPTY_LIST;
    private JTree classTree;
    private JList invList;
    private ModelClass selectedClass = null;
    private JPanel rightButtonPanel;
    private java.util.List selectionListeners = new LinkedList();
    
    
    /**
     * Creates and displays a dialog box asking the user to select a set of 
     * invariants.
     * @param modelClasses the classes to choose invariants from
     */
    public ClassInvariantSelectionPanel( Set modelClasses, 
                                         boolean useThroughoutInvs,
                                         ModelClass defaultClass,
                                         boolean selectDefaultInvs) {
        
        this.modelClasses      = modelClasses;
        this.useThroughoutInvs = useThroughoutInvs;
        
        //create class tree
        classTree = buildClassTree(modelClasses);
        classTree.addTreeSelectionListener(new TreeSelectionListener() {
            public void valueChanged(TreeSelectionEvent e) {
                DefaultMutableTreeNode selectedNode =
                  (DefaultMutableTreeNode)(e.getPath().getLastPathComponent());
                TreeEntry te = (TreeEntry)(selectedNode.getUserObject());
                Debug.assertTrue(!selectedNode.isLeaf() 
                                 || te.modelClass != null);
                selectedClass = te.modelClass;
                updateInvList();
            }
        });
        classTree.setCellRenderer(new DefaultTreeCellRenderer() {
            private final Color MEDIUMGREEN = new Color(80, 150, 0);
            private final Color DARKGREEN = new Color(0, 120, 90);
            private final Font BOLDFONT = ClassInvariantSelectionPanel.this.getFont().deriveFont(Font.BOLD, 10);
            public Component getTreeCellRendererComponent(JTree tree,
                                                          Object value,
                                                          boolean selected,
                                                          boolean expanded,
                                                          boolean leaf,
                                                          int row,
                                                          boolean hasFocus) {
                DefaultMutableTreeNode node = (DefaultMutableTreeNode)value;
                TreeEntry te = (TreeEntry)(node.getUserObject());
                if(te.numSelectedInvs == te.numInvs) {
                    setTextNonSelectionColor(MEDIUMGREEN);
                    setTextSelectionColor(MEDIUMGREEN);
                } else if(te.numSelectedInvs > 0) {
                    setTextNonSelectionColor(DARKGREEN);
                    setTextSelectionColor(DARKGREEN);
                } else {
                    setTextNonSelectionColor(Color.BLACK);
                    setTextSelectionColor(Color.BLACK);
                }
                setFont(BOLDFONT);
                return super.getTreeCellRendererComponent(tree,
                                                          value,
                                                          selected,
                                                          expanded,
                                                          leaf,
                                                          row,
                                                          hasFocus);
            }
        });
        
        //create inv list
        invList = new JList();
        invList.setSelectionMode(ListSelectionModel
                                 .MULTIPLE_INTERVAL_SELECTION);
        invList.addListSelectionListener(new ListSelectionListener() {
            public void valueChanged(ListSelectionEvent e) {
                if(e.getValueIsAdjusting()) {
                    return;
                }
                
                ListModel model = invList.getModel();
                int firstIndex = e.getFirstIndex();
                int lastIndex = Math.min(e.getLastIndex(), model.getSize() - 1);             
                for(int i = firstIndex; i <= lastIndex; i++) {
                    ClassInvariant inv 
                            = (ClassInvariant)(model.getElementAt(i));
                    if(invList.isSelectedIndex(i)) {
                        addToSelection(inv);
                    } else {
                        removeFromSelection(inv);
                    }
                }
                fireSelectionChanged(e);
            }
        });
        
        //create list panel
        JPanel listPanel = new JPanel();
        listPanel.setLayout(new BoxLayout(listPanel, BoxLayout.X_AXIS));
        add(listPanel);
        
        //create class scroll pane
        JScrollPane classScrollPane = new JScrollPane(classTree);
        classScrollPane.setBorder(new TitledBorder("Classes"));
        Dimension classScrollPaneDim = new Dimension(220, 400);
        classScrollPane.setPreferredSize(classScrollPaneDim);
        classScrollPane.setMinimumSize(classScrollPaneDim);
        listPanel.add(classScrollPane);
        
        //create invariant scroll pane
        JScrollPane invScrollPane = new JScrollPane(invList);
        invScrollPane.setBorder(new TitledBorder((useThroughoutInvs 
                                                  ? "Throughout invariants" 
                                                  : "Invariants")));
        Dimension invScrollPaneDim = new Dimension(440, 400);
        invScrollPane.setPreferredSize(invScrollPaneDim);
        invScrollPane.setMinimumSize(invScrollPaneDim);
        listPanel.add(invScrollPane);
    
        //create button panel
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new BoxLayout(buttonPanel, BoxLayout.X_AXIS));
        add(buttonPanel);
        Dimension buttonDim = new Dimension(95, 25);
        
        //create left button panel
        JPanel leftButtonPanel = new JPanel();
        leftButtonPanel.setLayout(new FlowLayout(FlowLayout.LEFT, 5, 5));
        buttonPanel.add(leftButtonPanel);
        
        //create right button panel
        rightButtonPanel = new JPanel();
        rightButtonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        buttonPanel.add(rightButtonPanel);
        
        //create "select all" button
        JButton selectButton = new JButton("Select all");
        selectButton.setPreferredSize(buttonDim);
        selectButton.setMinimumSize(buttonDim);
        selectButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                selectAll();
                updateInvList();
            }
        });
        leftButtonPanel.add(selectButton);
        
        //create "unselect all" button
        JButton unselectButton = new JButton("Unselect all");
        unselectButton.setPreferredSize(buttonDim);
        unselectButton.setMinimumSize(buttonDim);
        unselectButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                unselectAll();
                updateInvList();
            }
        });
        leftButtonPanel.add(unselectButton);
    
        
        //set default selection
        if(selectDefaultInvs) {
            selectAllForClass(defaultClass);
        }
        openClassInTree(defaultClass);
        
        //show dialog
        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));                
    }
    
    public JPanel getButtonPanel() {
        return rightButtonPanel;
    }
    
    public void addInvariantSelectionListener(ListSelectionListener listener) {
        selectionListeners.add(listener);        
    }
    
    private void fireSelectionChanged(ListSelectionEvent e) {
        Iterator it = selectionListeners.iterator();
        while (it.hasNext()) {
            ((ListSelectionListener)it.next()).valueChanged(e);
        }
    }
    
    
    private ListOfClassInvariant getRelevantInvs(ModelClass modelClass) {
        if(useThroughoutInvs) {
            return modelClass.getMyThroughoutClassInvariants();
        } else {
            return modelClass.getMyClassInvariants();
        }
    }
    
    
    private DefaultMutableTreeNode getChildByString(
                                            DefaultMutableTreeNode parentNode, 
                                            String childString) {
        int numChildren = parentNode.getChildCount();
        for(int i = 0; i < numChildren; i++) {
            DefaultMutableTreeNode childNode 
                    = (DefaultMutableTreeNode)(parentNode.getChildAt(i));
          
            TreeEntry te = (TreeEntry)(childNode.getUserObject());
            if(childString.equals(te.string)) {
                return childNode;
            }
        }
        return null;
    }
    
    
    private void insertIntoClassTree(DefaultMutableTreeNode rootNode, 
                                     ModelClass modelClass) {
        String fullClassName = modelClass.getFullClassName();
        int length = fullClassName.length();
        int index = -1;
        DefaultMutableTreeNode node = rootNode;
        
        do {
            //get next part of the name
            int lastIndex = index;
            index = fullClassName.indexOf(".", ++index);
            if(index == -1) {
                index = length;
            }
            String namePart = fullClassName.substring(lastIndex + 1, index);
            
            //try to get child node; otherwise, create and insert it
            DefaultMutableTreeNode childNode = 
		getChildByString(node, namePart);
            if(childNode == null) {
                TreeEntry te = new TreeEntry(namePart);
                childNode = new DefaultMutableTreeNode(te);
                node.add(childNode);
            }
            
            //go down to child node
            node = childNode;
        } while(index != length);
        
        //save model class in leaf
        TreeEntry te = (TreeEntry)(node.getUserObject());
        te.modelClass = modelClass;
    }
    
    
    private void setInvCounters(DefaultMutableTreeNode node) {
        int numInvs = 0;
        
        int numChildren = node.getChildCount();
        for(int i = 0; i < numChildren; i++) {
            DefaultMutableTreeNode childNode 
                    = (DefaultMutableTreeNode)(node.getChildAt(i));
            setInvCounters(childNode);
            TreeEntry te = (TreeEntry)(childNode.getUserObject());
            numInvs += te.numInvs;
        }
        
        TreeEntry te = (TreeEntry)(node.getUserObject());
        if(te.modelClass != null) {
            numInvs += getRelevantInvs(te.modelClass).size();
        }
        
        te.numInvs = numInvs;
    }
    
    
    private void setSelectedInvCounters(DefaultMutableTreeNode node) {
        int numSelectedInvs = 0;
        
        int numChildren = node.getChildCount();
        for(int i = 0; i < numChildren; i++) {
            DefaultMutableTreeNode childNode 
                    = (DefaultMutableTreeNode)(node.getChildAt(i));
            setSelectedInvCounters(childNode);
            TreeEntry te = (TreeEntry)(childNode.getUserObject());
            numSelectedInvs += te.numSelectedInvs;
        }
        
        TreeEntry te = (TreeEntry)(node.getUserObject());
        if(te.modelClass != null) {
            ListOfClassInvariant invs = getRelevantInvs(te.modelClass);
            IteratorOfClassInvariant it = invs.iterator();
            while(it.hasNext()) {
                if(selectedInvs.contains(it.next())) {
                    numSelectedInvs++;
                }
            }
        }
        
        te.numSelectedInvs = numSelectedInvs;
    }
    
    
    private JTree buildClassTree(Set modelClasses) {
        //sort classes alphabetically
        Object[] mca = modelClasses.toArray();
        Arrays.sort(mca, new Comparator() {
            public int compare(Object o1, Object o2) {
                ModelClass mc1 = (ModelClass)o1;
                ModelClass mc2 = (ModelClass)o2;
                return mc1.getFullClassName().compareTo(mc2.getFullClassName());
            }
        });
        
        //build tree
        TreeEntry rootEntry = new TreeEntry("");
        DefaultMutableTreeNode rootNode = 
	    new DefaultMutableTreeNode(rootEntry);
        for(int i = 0; i < mca.length; i++) {
            ModelClass modelClass = (ModelClass)(mca[i]);
            if(getRelevantInvs(modelClass).size() > 0){
                insertIntoClassTree(rootNode, modelClass);
            }
        }
        
        //set inv counters
        setInvCounters(rootNode);
        
        JTree result = new JTree(new DefaultTreeModel(rootNode)); 
        //result.setRootVisible(false);
        return result;
    }
    
    
    private void addToSelection(ClassInvariant inv) {
        //make sure inv is not selected already
        if(selectedInvs.contains(inv)) {
            return;
        }
        
        //add it to the selection
        selectedInvs = selectedInvs.prepend(inv);
        
        //update selection counters in tree
        Object[] nodes = classTree.getSelectionPath().getPath();
        for(int i = 0; i < nodes.length; i++) {
            DefaultMutableTreeNode node = (DefaultMutableTreeNode)(nodes[i]);
            TreeEntry te = (TreeEntry)(node.getUserObject());
            te.numSelectedInvs++;
            Debug.assertTrue(te.numSelectedInvs > 0 
                             && te.numSelectedInvs <= te.numInvs);
            
        }
        classTree.repaint();
    }
    
    
    private void removeFromSelection(ClassInvariant inv) {
        //make sure inv is currently selected
        if(!selectedInvs.contains(inv)) {
            return;
        }
        
        //remove it from the selection
        selectedInvs = selectedInvs.removeFirst(inv);
        
        //update selection counters in tree
        Object[] nodes = classTree.getSelectionPath().getPath();
        for(int i = 0; i < nodes.length; i++) {
            DefaultMutableTreeNode node = (DefaultMutableTreeNode)(nodes[i]);
            TreeEntry te = (TreeEntry)(node.getUserObject());
            te.numSelectedInvs--;
            Debug.assertTrue(te.numSelectedInvs >= 0 
                             && te.numSelectedInvs < te.numInvs);
        }
        classTree.repaint();
    }
    
    
    private void selectAllForClass(ModelClass modelClass) {
        //select invariants of this class
        selectedInvs = getRelevantInvs(modelClass);
        
        //update selection counters in tree
        DefaultMutableTreeNode rootNode
                = (DefaultMutableTreeNode)(classTree.getModel().getRoot());
        setSelectedInvCounters(rootNode);
        classTree.repaint();
    }
    
    
    private void selectAll() {
        //select all
        selectedInvs = SLListOfClassInvariant.EMPTY_LIST;
        Iterator it = modelClasses.iterator();
        while(it.hasNext()) {
            ModelClass modelClass = (ModelClass)(it.next());
            selectedInvs = selectedInvs.append(getRelevantInvs(modelClass));
        }
        
        //update selection counters in tree
        DefaultMutableTreeNode rootNode
                = (DefaultMutableTreeNode)(classTree.getModel().getRoot());
        setSelectedInvCounters(rootNode);
        classTree.repaint();
    }
    
    
    private void unselectAll() {
        //unselect all
        selectedInvs = SLListOfClassInvariant.EMPTY_LIST;
        
        //update selection counters in tree
        DefaultMutableTreeNode rootNode
                = (DefaultMutableTreeNode)(classTree.getModel().getRoot());
        setSelectedInvCounters(rootNode);
        classTree.repaint();
    }
    
    
    private void updateInvList() {     
        invList.setValueIsAdjusting(true);
        
        if(selectedClass == null) {
            invList.setListData(new Object[0]);
        } else {
            ListOfClassInvariant invariants = getRelevantInvs(selectedClass);
            invList.setListData(invariants.toArray());
            
            IteratorOfClassInvariant it = selectedInvs.iterator();
            while(it.hasNext()) {
                invList.setSelectedValue(it.next(), false);
            }
        }
        
        invList.setValueIsAdjusting(false);
    }
    
    
    private boolean openClassInTree(ModelClass modelClass) {
        //get tree path
        Vector pathVector = new Vector();
        
        String fullClassName = modelClass.getFullClassName();
        int length = fullClassName.length();
        int index = -1;
        DefaultMutableTreeNode node 
                = (DefaultMutableTreeNode)(classTree.getModel().getRoot());
        Debug.assertTrue(node!=null);        
        do {
            //save current node
            pathVector.add(node);
            
            //get next part of the name
            int lastIndex = index;
            index = fullClassName.indexOf(".", ++index);
            if(index == -1) {
                index = length;
            }
            String namePart = fullClassName.substring(lastIndex + 1, index);
            
            //get child node, go down to it
            DefaultMutableTreeNode childNode = 
		getChildByString(node, namePart);
	    if (childNode == null) {
		return false;
	    }
            node = childNode;
        } while(index != length);
        TreePath incompletePath = new TreePath(pathVector.toArray());
        
        TreePath path = incompletePath.pathByAddingChild(node);
        
        classTree.expandPath(incompletePath);
        classTree.setSelectionRow(classTree.getRowForPath(path));
        return true;
    }
    
    /**
     * Returns the selected set of invariants.
     */
    public ListOfClassInvariant getClassInvariants() {
        return selectedInvs;
    }
    
    public JList getInvList() {
        return invList;
    }
    
    
    private static class TreeEntry {
        public String string;
        public ModelClass modelClass = null;        
        public int numInvs = 0;
        public int numSelectedInvs = 0;
        
        public TreeEntry(String string) {
            this.string = string;
        }
        
        public String toString() {
            return string;
        }
    }
}
