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

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.util.Pair;


class ClassTree extends JTree {
    
    private final Map<Pair<KeYJavaType,ObserverFunction>,Icon> targetIcons;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------    

    public ClassTree(boolean addContractTargets, 
	             boolean skipLibraryClasses,
	    	     Services services,
	    	     Map<Pair<KeYJavaType,ObserverFunction>,Icon> targetIcons) {
	super(new DefaultTreeModel(createTree(addContractTargets, 
					      skipLibraryClasses, 
					      services)));
	this.targetIcons = targetIcons;
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
		if(entry.target == null) {
		    result = super.getTreeCellRendererComponent(tree, 
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
		    
		    if(result instanceof JLabel) {
			((JLabel) result).setIcon(
				ClassTree.this.targetIcons.get(
		          new Pair<KeYJavaType,ObserverFunction>(
		        	  			entry.kjt, 
		        	                        entry.target)));
		    }
		}
		
		return result;
	    }
	});
    }
    
    
    public ClassTree(boolean addContractTargets, 
	             boolean skipLibraryClasses,
	    	     Services services) {
	this(addContractTargets, 
	     skipLibraryClasses, 
	     services, 
	     new HashMap<Pair<KeYJavaType,ObserverFunction>,Icon>());
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
    
    
    private static DefaultMutableTreeNode getChildByTarget(
	    				     DefaultMutableTreeNode parentNode,
	    				     ObserverFunction target) {
        int numChildren = parentNode.getChildCount();
        for(int i = 0; i < numChildren; i++) {
            DefaultMutableTreeNode childNode 
                    = (DefaultMutableTreeNode)(parentNode.getChildAt(i));
          
            Entry te = (Entry)(childNode.getUserObject());
            if(target.equals(te.target)) {
                return childNode;
            }
        }
        return null;	
    }
    
    
    private static void insertIntoTree(DefaultMutableTreeNode rootNode, 
	    			       KeYJavaType kjt,
	    			       boolean addContractTargets,
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
        
        //add all contract targets of kjt
        if(addContractTargets) {
            final ImmutableSet<ObserverFunction> targets
            	= services.getSpecificationRepository().getContractTargets(kjt);
            
            //sort targets alphabetically
            final ObserverFunction[] targetsArr
            	= targets.toArray(new ObserverFunction[targets.size()]);            
            Arrays.sort(targetsArr, new Comparator<ObserverFunction>() {
        	public int compare(ObserverFunction o1, ObserverFunction o2) {
        	    if(o1 instanceof ProgramMethod 
        	       && !(o2 instanceof ProgramMethod)) {
        		return -1;
        	    } else if(!(o1 instanceof ProgramMethod) 
        		      && o2 instanceof ProgramMethod) {
        		return 1;
        	    } else {
        		return o1.name()
        		         .toString()
        		         .compareTo(o2.name().toString());
        	    }
        	}
            });
            
            for(ObserverFunction target : targetsArr) {
        	StringBuffer sb = new StringBuffer();
        	if(target instanceof ProgramMethod) {
        	    sb.append(((ProgramMethod)target).getName());
        	} else {
        	    sb.append(target.name());
        	}
        	if(target.getNumParams() > 0 || target instanceof ProgramMethod) {
        	    sb.append("(");
        	}
        	for(KeYJavaType paramType : target.getParamTypes()) {
        	    sb.append(paramType.getSort().name() + ", ");
        	}
        	if(target.getNumParams() > 0) {
        	    sb.setLength(sb.length() - 2);
        	}
        	if(target.getNumParams() > 0 || target instanceof ProgramMethod) {
        	    sb.append(")");
        	}
        	Entry te = new Entry(sb.toString());
        	DefaultMutableTreeNode childNode 
        	= new DefaultMutableTreeNode(te);
        	te.kjt = kjt;
        	te.target = target;
        	node.add(childNode);
            }
        }
    }

    
    private static DefaultMutableTreeNode createTree(boolean addContractTargets,
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
            insertIntoTree(rootNode, kjtsarr[i], addContractTargets, services);
        }
        
        return rootNode;
    }
    
    
    private void open(KeYJavaType kjt, ObserverFunction target) {
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
        if(target != null) {
            DefaultMutableTreeNode methodNode = getChildByTarget(node, target);
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
    
    
    public void select(KeYJavaType kjt, ObserverFunction target) {
	open(kjt, target);
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
        public ObserverFunction target = null;
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
