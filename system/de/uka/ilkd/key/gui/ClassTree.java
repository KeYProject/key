// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.util.*;

import javax.swing.Icon;
import javax.swing.JLabel;
import javax.swing.JTree;
import javax.swing.tree.*;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.util.Pair;


class ClassTree extends JTree {
    
    private static final String INIT_NAME 
        =  ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER;
    
    private final Map<Pair<ProgramMethod,KeYJavaType>,Icon> methodIcons;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------    

    public ClassTree(boolean addOperations, 
	             boolean skipLibraryClasses,
	    	     Services services,
	    	     Map<Pair<ProgramMethod,KeYJavaType>,Icon> methodIcons) {
	super(new DefaultTreeModel(createTree(addOperations, 
					      skipLibraryClasses, 
					      services)));
	this.methodIcons = methodIcons;
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
		if(entry.pm == null) {
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
			((JLabel) result).setIcon(
				ClassTree.this.methodIcons.get(
		          new Pair<ProgramMethod,KeYJavaType>(entry.pm, 
		        	                              entry.kjt)));
		    }
		}
		
		return result;
	    }
	});
    }
    
    
    public ClassTree(boolean addOperations, 
	             boolean skipLibraryClasses,
	    	     Services services) {
	this(addOperations, 
	     skipLibraryClasses, 
	     services, 
	     new HashMap<Pair<ProgramMethod,KeYJavaType>,Icon>());
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
    
    
    private static DefaultMutableTreeNode getChildByProgramMethod(
	    				     DefaultMutableTreeNode parentNode,
	    				     ProgramMethod pm) {
        int numChildren = parentNode.getChildCount();
        for(int i = 0; i < numChildren; i++) {
            DefaultMutableTreeNode childNode 
                    = (DefaultMutableTreeNode)(parentNode.getChildAt(i));
          
            Entry te = (Entry)(childNode.getUserObject());
            if(pm.equals(te.pm)) {
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
            ImmutableList<ProgramMethod> pms 
            	= services.getJavaInfo()
            		  .getAllProgramMethodsLocallyDeclaredOrAutomaticOverride(kjt);
                          //.getAllProgramMethodsLocallyDeclared(kjt);
            Iterator<ProgramMethod> it = pms.iterator();
            while(it.hasNext()) {
                ProgramMethod pm = it.next();
                if ((!pm.isImplicit() || pm.getName().equals(INIT_NAME))
                        && pm.getMethodDeclaration().getBody() != null) {
                    StringBuffer sb = new StringBuffer(pm.getName());
                    sb.append("(");
                    for(int i = 0, n = pm.getParameterDeclarationCount(); 
                        i < n; i++) {
                        sb.append(pm.getParameterDeclarationAt(i) + ", ");
                    }
                    if(pm.getParameterDeclarationCount() > 0) {
                        sb.setLength(sb.length() - 2);
                    }
                    sb.append(")");
                    Entry te = new Entry(sb.toString());
                    DefaultMutableTreeNode childNode 
                    	= new DefaultMutableTreeNode(te);
                    te.kjt = kjt;
                    te.pm = pm;
                    node.add(childNode);
                }
            }
        }
    }

    
    private static DefaultMutableTreeNode createTree(boolean addOperations,
	    					     boolean skipLibraryClasses,
	    					     Services services) {
	//get all classes
	final Set<KeYJavaType> kjts 
		= services.getJavaInfo().getAllKeYJavaTypes();
	final Iterator<KeYJavaType> it = kjts.iterator();
	while(it.hasNext()) {
	    KeYJavaType kjt = it.next();
	    if(!(kjt.getJavaType() instanceof ClassDeclaration 
		 || kjt.getJavaType() instanceof InterfaceDeclaration) 
		 || (((TypeDeclaration) kjt.getJavaType()).isLibraryClass() 
		       && skipLibraryClasses)) {
		it.remove();
	    }
	}
	
        //sort classes alphabetically
        final KeYJavaType[] kjtsarr 
        	= kjts.toArray(new KeYJavaType[kjts.size()]);
        Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
            public int compare(KeYJavaType o1, KeYJavaType o2) {
                return o1.getFullName().compareTo(o2.getFullName());
            }
        });
        
        //build tree
        DefaultMutableTreeNode rootNode 
        	= new DefaultMutableTreeNode(new Entry(""));
        for(int i = 0; i < kjtsarr.length; i++) {
            insertIntoTree(rootNode, kjtsarr[i], addOperations, services);
        }
        
        return rootNode;
    }
    
    
    private void open(KeYJavaType kjt, ProgramMethod pm) {
        //get tree path to class
        Vector<DefaultMutableTreeNode> pathVector 
        	= new Vector<DefaultMutableTreeNode>();
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
        
        //extend tree path to method
        if(pm != null) {
            DefaultMutableTreeNode methodNode 
        	= getChildByProgramMethod(node, pm);
            if(methodNode != null) {
        	incompletePath = path;            
        	path = path.pathByAddingChild(methodNode);
            }
        }
        
        //open and select
        expandPath(incompletePath);
        setSelectionRow(getRowForPath(path));
    }
    

    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public void select(KeYJavaType kjt) {
	open(kjt, null);
    }
    
    
    public void select(ProgramMethod pm) {
	open(pm.getContainerType(), pm);
    }
    
    
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
