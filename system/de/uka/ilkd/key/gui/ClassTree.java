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

import java.awt.Component;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;

import javax.swing.JLabel;
import javax.swing.JTree;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;
import javax.swing.tree.TreeSelectionModel;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.logic.op.IteratorOfProgramMethod;
import de.uka.ilkd.key.logic.op.ListOfProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;


class ClassTree extends JTree {
    
    private static final String INIT_NAME 
        =  ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------    

    public ClassTree(boolean addOperations, 
	    	     KeYJavaType defaultClass,
	    	     Services services) {
	super(new DefaultTreeModel(createTree(addOperations, services)));
	if(defaultClass != null) {
	    open(defaultClass);
	}
	getSelectionModel().setSelectionMode(
				TreeSelectionModel.SINGLE_TREE_SELECTION);
	setCellRenderer(new DefaultTreeCellRenderer() {
	    public Component getTreeCellRendererComponent(JTree tree,
						      	  Object value,
						      	  boolean sel,
						      	  boolean expanded,
						      	  boolean leaf,
						      	  int row,
						      	  boolean hasFocus) {
		DefaultMutableTreeNode node = (DefaultMutableTreeNode) value;
		Entry entry = (Entry) node.getUserObject();
		
		Component result;
		if(entry.kjt != null) {
		    result =  super.getTreeCellRendererComponent(tree, 
			    				      	 value, 
			    				      	 sel, 
			    				      	 expanded, 
			    				      	 true, 
			    				      	 row, 
			    				      	 hasFocus);
		} else {
		    result = super.getTreeCellRendererComponent(tree, 
							     	value, 
							     	sel, 
							     	expanded, 
							     	leaf, 
							     	row, 
							     	hasFocus);
		    
		    if(entry.pm != null && result instanceof JLabel) {
			((JLabel) result).setIcon(null);
		    }
		}
		
		return result;
	    }
	});
    }
    
    
        
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------    
    
    private static DefaultMutableTreeNode getChildByString(
                                            DefaultMutableTreeNode parentNode, 
                                            String childString) {
        int numChildren = parentNode.getChildCount();
        for(int i = 0; i < numChildren; i++) {
            DefaultMutableTreeNode childNode 
                    = (DefaultMutableTreeNode)(parentNode.getChildAt(i));
          
            Entry te = (Entry)(childNode.getUserObject());
            if(childString.equals(te.string)) {
                return childNode;
            }
        }
        return null;
    }
    
    
    private static void insertIntoTree(DefaultMutableTreeNode rootNode, 
	    			       KeYJavaType kjt,
	    			       boolean addOperations,
	    			       Services services) {	
        String fullClassName = kjt.getFullName();
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
            DefaultMutableTreeNode childNode = getChildByString(node, namePart);
            if(childNode == null) {
                Entry te = new Entry(namePart);
                childNode = new DefaultMutableTreeNode(te);
                node.add(childNode);
            }
            
            //go down to child node
            node = childNode;
        } while(index != length);
        
        //save kjt in leaf
        ((Entry) node.getUserObject()).kjt = kjt;
        
        //add all operations of kjt
        if(addOperations) {
            ListOfProgramMethod pms 
            	= services.getJavaInfo()
                          .getAllProgramMethodsLocallyDeclared(kjt);
            IteratorOfProgramMethod it = pms.iterator();
            while(it.hasNext()) {
                ProgramMethod pm = it.next();
                if ((!pm.isImplicit() || pm.getName().equals(INIT_NAME))
                        && pm.getMethodDeclaration().getBody() != null) {
                    StringBuffer sb = new StringBuffer(pm.getName());
                    sb.append("(");
                    for(int i = 0; i < pm.getParameterDeclarationCount(); i++) {
                        sb.append(pm.getParameterDeclarationAt(i));
                    }
                    sb.append(")");
                    Entry te = new Entry(sb.toString());
                    DefaultMutableTreeNode childNode = new DefaultMutableTreeNode(te);
                    te.pm = pm;
                    node.add(childNode);
                }
            }
        }
    }

    
    private static DefaultMutableTreeNode createTree(boolean addOperations,
	    					     Services services) {
	//get all classes
	Set kjts = services.getJavaInfo().getAllKeYJavaTypes();
	Iterator it = kjts.iterator();
	while(it.hasNext()) {
	    KeYJavaType kjt = (KeYJavaType) it.next();
	    if(!(kjt.getJavaType() instanceof ClassDeclaration 
		 || kjt.getJavaType() instanceof InterfaceDeclaration)) {
		it.remove();
	    }
	}
	
        //sort classes alphabetically
        Object[] kjtsarr = kjts.toArray();
        Arrays.sort(kjtsarr, new Comparator() {
            public int compare(Object o1, Object o2) {
                KeYJavaType kjt1 = (KeYJavaType)o1;
                KeYJavaType kjt2 = (KeYJavaType)o2;
                return kjt1.getFullName().compareTo(kjt2.getFullName());
            }
        });
        
        //build tree
        DefaultMutableTreeNode rootNode 
        	= new DefaultMutableTreeNode(new Entry(""));
        for(int i = 0; i < kjtsarr.length; i++) {
            KeYJavaType kjt = (KeYJavaType)(kjtsarr[i]);
            insertIntoTree(rootNode, kjt, addOperations, services);
        }
        
        return rootNode;
    }
    
    
    private void open(KeYJavaType kjt) {
        //get tree path
        Vector pathVector = new Vector();
        
        String fullClassName = kjt.getFullName();
        int length = fullClassName.length();
        int index = -1;
        DefaultMutableTreeNode node 
                = (DefaultMutableTreeNode) getModel().getRoot();
        assert node != null;        
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
            DefaultMutableTreeNode childNode = getChildByString(node, namePart);
	    assert childNode != null;
            node = childNode;
        } while(index != length);
        
        TreePath incompletePath = new TreePath(pathVector.toArray());
        TreePath path = incompletePath.pathByAddingChild(node);
        
        expandPath(incompletePath);
        setSelectionRow(getRowForPath(path));
    }
    

    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public DefaultMutableTreeNode getRootNode() {
	return (DefaultMutableTreeNode) getModel().getRoot();
    }
    
    
    public DefaultMutableTreeNode getSelectedNode() {
        TreePath path = getSelectionPath();
        return path != null 
               ? (DefaultMutableTreeNode) path.getLastPathComponent()
               : null;
    }
    
    
    public Entry getSelectedEntry() {
        DefaultMutableTreeNode node = getSelectedNode();
        return node != null ? (Entry) node.getUserObject() : null;
    }

    
    
    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------    
    
    static class Entry {
        public final String string;
        public KeYJavaType kjt = null;
        public ProgramMethod pm = null;
        public int numMembers = 0;
        public int numSelectedMembers = 0;      
        
        public Entry(String string) {
            this.string = string;
        }
        
        public String toString() {
            return string;
        }
    }
}
