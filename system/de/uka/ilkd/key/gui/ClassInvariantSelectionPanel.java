// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.gui;


import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Iterator;
import java.util.Set;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.*;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.RTSJProfile;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.*;


/**
 * A panel for selecting class invariants.
 */
class ClassInvariantSelectionPanel extends JPanel {

    private final Services services;
    private final SpecificationRepository specRepos;
    private final boolean useThroughoutInvs;
    
    private final ClassTree classTree;
    private final JList invList;
    private final JPanel leftButtonPanel;
    private final JPanel rightButtonPanel;

    private SetOfClassInvariant selectedInvs 
            = SetAsListOfClassInvariant.EMPTY_SET;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------    
    
    public ClassInvariantSelectionPanel(Services services,
                                        boolean useThroughoutInvs,
                                        KeYJavaType defaultClass,
                                        boolean selectDefaultInvs) {
        this.services          = services;
        this.specRepos         = services.getSpecificationRepository();
        this.useThroughoutInvs = useThroughoutInvs;
                        
        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS)); 
        
        //create list panel
        JPanel listPanel = new JPanel();
        listPanel.setLayout(new BoxLayout(listPanel, BoxLayout.X_AXIS));
        listPanel.setMinimumSize(new Dimension(660, 435));
        add(listPanel);
        
        //create class scroll pane
        JScrollPane classScrollPane = new JScrollPane();
        classScrollPane.setBorder(new TitledBorder("Classes"));
        Dimension classScrollPaneDim = new Dimension(220, 435);
        classScrollPane.setMinimumSize(classScrollPaneDim);
        listPanel.add(classScrollPane);
        
        //create class tree
        classTree = new ClassTree(false, defaultClass, null, services);
        setInvCounters(classTree.getRootNode());
        classTree.addTreeSelectionListener(new TreeSelectionListener() {
            public void valueChanged(TreeSelectionEvent e) {
                updateInvList();
            }
        });
        classTree.setCellRenderer(new DefaultTreeCellRenderer() {
            private final Color MEDIUMGREEN = new Color(80, 150, 0);
            private final Color DARKGREEN = new Color(0, 120, 90);
            private final Font BOLDFONT 
            	= ClassInvariantSelectionPanel.this
            				      .getFont()
            				      .deriveFont(Font.BOLD, 10);

            public Component getTreeCellRendererComponent(JTree tree,
                                                          Object value,
                                                          boolean selected,
                                                          boolean expanded,
                                                          boolean leaf,
                                                          int row,
                                                          boolean hasFocus) {
        	
                DefaultMutableTreeNode node = (DefaultMutableTreeNode)value;
                ClassTree.Entry te = (ClassTree.Entry) node.getUserObject();
                if(te.numSelectedMembers == te.numMembers 
                	&& te.numMembers > 0) {
                    setTextNonSelectionColor(MEDIUMGREEN);
                    setTextSelectionColor(MEDIUMGREEN);
                } else if(te.numSelectedMembers > 0) {
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
        classScrollPane.setViewportView(classTree);
        
        //create invariant scroll pane
        JScrollPane invScrollPane = new JScrollPane();
        invScrollPane.setBorder(new TitledBorder((useThroughoutInvs 
                                                  ? "Throughout invariants" 
                                                  : "Invariants")));
        Dimension invScrollPaneDim = new Dimension(440, 435);
        invScrollPane.setPreferredSize(invScrollPaneDim);
        invScrollPane.setMinimumSize(invScrollPaneDim);
        listPanel.add(invScrollPane);
        
        //create inv list
        invList = new JList();
        invList.setSelectionMode(ListSelectionModel
                                 .MULTIPLE_INTERVAL_SELECTION);
        final Services finalServices = services;
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
            }
        });
        invList.setCellRenderer(new DefaultListCellRenderer() {
            private final Font PLAINFONT = getFont().deriveFont(Font.PLAIN);
            
	    public Component getListCellRendererComponent(
                                		    JList list,
                                		    Object value,
                                		    int index,
                                		    boolean isSelected,
                                		    boolean cellHasFocus) {
		ClassInvariant inv = (ClassInvariant) value;
		Component supComp 
		    	= super.getListCellRendererComponent(list, 
		    					     value, 
		    					     index, 
		    					     isSelected, 
		    					     cellHasFocus);		
		
		//create label and enclosing panel
		JLabel label = new JLabel();
		label.setText(inv.getHTMLText(finalServices));
		label.setFont(PLAINFONT);
		FlowLayout lay = new FlowLayout();
		lay.setAlignment(FlowLayout.LEFT);
		JPanel result = new JPanel(lay);
		result.add(label);
		label.setVerticalAlignment(SwingConstants.TOP);
		
		//set background color
		result.setBackground(supComp.getBackground());

		//set border
		TitledBorder border = new TitledBorder(
				BorderFactory.createEtchedBorder(),
                                inv.getName());
		border.setTitleFont(border.getTitleFont()
					  .deriveFont(Font.BOLD));
		result.setBorder(border);
		
		return result;
	    }
        });
        invScrollPane.setViewportView(invList);
    
        //create button panel
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new BoxLayout(buttonPanel, BoxLayout.X_AXIS));
        Dimension buttonDim = new Dimension(110, 27);
        buttonPanel.setMaximumSize(new Dimension(Integer.MAX_VALUE, 
                                                 (int)buttonDim.getHeight() 
                                                     + 10));
        add(buttonPanel);
        
        //create left button panel
        leftButtonPanel = new JPanel();
        leftButtonPanel.setLayout(new FlowLayout(FlowLayout.LEFT, 5, 5));
        buttonPanel.add(leftButtonPanel);
                
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
        
        //create right button panel
        rightButtonPanel = new JPanel();
        rightButtonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        buttonPanel.add(rightButtonPanel);
    
        //set default selection
        if(selectDefaultInvs) {
            selectAllForClass(defaultClass);
            Profile prof = services.getProof()!=null ? services.getProof().getSettings().getProfile() :
                ProofSettings.DEFAULT_SETTINGS.getProfile();
            if(prof instanceof RTSJProfile){
                addAllRealtimeInvs();
            }
        }
        updateInvList();
    }
    

    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------    
    
    private SetOfClassInvariant getRelevantInvs(KeYJavaType kjt) {
        if(useThroughoutInvs) {
            return specRepos.getThroughoutClassInvariants(kjt);
        } else {
            return specRepos.getClassInvariants(kjt);
        }
    }
    
    
    private void setInvCounters(DefaultMutableTreeNode node) {
        int numMembers = 0;
        
        int numChildren = node.getChildCount();
        for(int i = 0; i < numChildren; i++) {
            DefaultMutableTreeNode childNode 
                    = (DefaultMutableTreeNode) node.getChildAt(i);
            setInvCounters(childNode);
            ClassTree.Entry te = (ClassTree.Entry)(childNode.getUserObject());
            numMembers += te.numMembers;
        }

        ClassTree.Entry te = (ClassTree.Entry) node.getUserObject();
        if(te.kjt != null) {
            numMembers += getRelevantInvs(te.kjt).size();
        }
        
        te.numMembers = numMembers;
    }
    
    
    private void setSelectedInvCounters(DefaultMutableTreeNode node) {
        int numSelectedMembers = 0;
        
        int numChildren = node.getChildCount();
        for(int i = 0; i < numChildren; i++) {
            DefaultMutableTreeNode childNode 
                    = (DefaultMutableTreeNode) node.getChildAt(i);
            setSelectedInvCounters(childNode);
            ClassTree.Entry te = (ClassTree.Entry) childNode.getUserObject();
            numSelectedMembers += te.numSelectedMembers;
        }
        
        ClassTree.Entry te = (ClassTree.Entry) node.getUserObject();
        if(te.kjt != null) {
            SetOfClassInvariant invs = getRelevantInvs(te.kjt);
            IteratorOfClassInvariant it = invs.iterator();
            while(it.hasNext()) {
                if(selectedInvs.contains(it.next())) {
                    numSelectedMembers++;
                }
            }
        }
        
        te.numSelectedMembers = numSelectedMembers;
    }
        
    
    private void addToSelection(ClassInvariant inv) {
        //make sure inv is not selected already
        if(selectedInvs.contains(inv)) {
            return;
        }
        
        //add it to the selection
        selectedInvs = selectedInvs.add(inv);
        
        //update selection counters in tree
        Object[] nodes = classTree.getSelectionPath().getPath();
        for(int i = 0; i < nodes.length; i++) {
            DefaultMutableTreeNode node = (DefaultMutableTreeNode)(nodes[i]);
            ClassTree.Entry te = (ClassTree.Entry) node.getUserObject();
            te.numSelectedMembers++;
            assert te.numSelectedMembers > 0 
                   && te.numSelectedMembers <= te.numMembers;
            
        }
        classTree.repaint();
    }
    
    
    private void removeFromSelection(ClassInvariant inv) {
        //make sure inv is currently selected
        if(!selectedInvs.contains(inv)) {
            return;
        }
        
        //remove it from the selection
        selectedInvs = selectedInvs.remove(inv);
        
        //update selection counters in tree
        Object[] nodes = classTree.getSelectionPath().getPath();
        for(int i = 0; i < nodes.length; i++) {
            DefaultMutableTreeNode node = (DefaultMutableTreeNode)(nodes[i]);
            ClassTree.Entry te = (ClassTree.Entry) node.getUserObject();
            te.numSelectedMembers--;
            assert te.numSelectedMembers >= 0 
                   && te.numSelectedMembers < te.numMembers;
        }
        classTree.repaint();
    }
    
    
    private void selectAllForClass(KeYJavaType kjt) {
        //select invariants of this class
        selectedInvs = getRelevantInvs(kjt);        
        
        //update selection counters in tree
        DefaultMutableTreeNode rootNode
                = (DefaultMutableTreeNode) classTree.getModel().getRoot();
        setSelectedInvCounters(rootNode);
        classTree.repaint();
    }
    
    
    private void selectAll() {
        //select all
        selectedInvs = SetAsListOfClassInvariant.EMPTY_SET;
	final Set<KeYJavaType> kjts = services.getJavaInfo().getAllKeYJavaTypes();
	final Iterator<KeYJavaType> it = kjts.iterator();
        while (it.hasNext()) {
            final KeYJavaType kjt = it.next();            
            selectedInvs = selectedInvs.union(getRelevantInvs(kjt));
        }
        
        //update selection counters in tree
        DefaultMutableTreeNode rootNode
                = (DefaultMutableTreeNode) classTree.getModel().getRoot();
        setSelectedInvCounters(rootNode);
        classTree.repaint();
    }
    
    private void addAllRealtimeInvs() {
        //select all invariants in javax.realtime.*
        final Set<KeYJavaType> kjts = services.getJavaInfo().getAllKeYJavaTypes();
        final Iterator<KeYJavaType> it = kjts.iterator();
        while (it.hasNext()) {
            final KeYJavaType kjt = it.next();     
            if(kjt.getFullName().indexOf("javax.realtime")!=-1){
                selectedInvs = selectedInvs.union(getRelevantInvs(kjt));
            }
        }
        
        //update selection counters in tree
        DefaultMutableTreeNode rootNode
                = (DefaultMutableTreeNode) classTree.getModel().getRoot();
        setSelectedInvCounters(rootNode);
        classTree.repaint();
    }
    
    
    private void unselectAll() {
        //unselect all
        selectedInvs = SetAsListOfClassInvariant.EMPTY_SET;
        
        //update selection counters in tree
        DefaultMutableTreeNode rootNode
                = (DefaultMutableTreeNode) classTree.getModel().getRoot();
        setSelectedInvCounters(rootNode);
        classTree.repaint();
    }
    
    
    private void updateInvList() {     
        invList.setValueIsAdjusting(true);
        
       	ClassTree.Entry selectedEntry = classTree.getSelectedEntry();

        if(selectedEntry == null || selectedEntry.kjt == null) {
            invList.setListData(new Object[0]);
        } else {
            SetOfClassInvariant invariants = getRelevantInvs(selectedEntry.kjt);
            ClassInvariant[] listData = invariants.toArray();
            invList.setListData(listData);
            
            for(int i = 0; i < listData.length; i++) {
                if(selectedInvs.contains(listData[i])) {
                    invList.addSelectionInterval(i, i);
                }
            }
        }
        
        invList.setValueIsAdjusting(false);
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------    

    public JPanel getButtonPanel() {
        return rightButtonPanel;
    }
    
    
    /**
     * Returns the selected set of invariants.
     */
    public SetOfClassInvariant getClassInvariants() {
        return selectedInvs;
    }
}
