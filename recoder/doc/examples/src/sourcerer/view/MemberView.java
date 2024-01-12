package sourcerer.view;

import java.awt.BorderLayout;
import java.awt.Component;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTree;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.TreeModelEvent;
import javax.swing.event.TreeModelListener;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreePath;
import javax.swing.tree.TreeSelectionModel;

import recoder.ModelElement;
import recoder.NamedModelElement;
import recoder.abstraction.ClassType;
import recoder.abstraction.ClassTypeContainer;
import recoder.abstraction.Constructor;
import recoder.abstraction.Field;
import recoder.abstraction.Member;
import recoder.abstraction.Method;
import recoder.abstraction.Package;
import recoder.abstraction.ProgramModelElement;
import recoder.convenience.Format;
import recoder.java.ProgramElement;
import recoder.service.NameInfo;
import recoder.util.Order;
import recoder.util.Sorting;
import sourcerer.Resources;
import sourcerer.SelectionModel;
import sourcerer.util.RecoderUtils;

/**
   Constructs an empty JTree with some initializations.   
*/
public class MemberView extends JPanel implements SelectionView {

    protected SelectionModel model;

    protected JTree tree;

    public MemberView(final SelectionModel model, NameInfo ni) {
	super(new BorderLayout());
	setName("Member Hierarchy");
	tree = new JTree(new MemberModel(ni));
	tree.setLargeModel(true); // optimizing; all cells have equal height
	tree.setCellRenderer(new MemberRenderer());
	tree.setRootVisible(false);
	tree.setShowsRootHandles(true);
	tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
	tree.putClientProperty("JTree.lineStyle", "Angled");
	tree.addTreeSelectionListener(selectionListener);
	add(new JScrollPane(tree));
	setModel(model);
    }

    public JTree getTree() {
	return tree;
    }

    public SelectionModel getModel() {
	return model;
    }

    /**
       Use setSelectionModel(null) to detach from the model.
     */
    public void setModel(SelectionModel model) {
	if (this.model != model) {
	    if (this.model != null) {
		this.model.removeChangeListener(changeListener);
	    }
	    if (model != null) {
		this.model = model;
		model.addChangeListener(changeListener);		
	    }
	    changeSelection();
	}
    }

    protected MemberRenderer getRenderer() {
	return (MemberRenderer)tree.getCellRenderer();
    }

    public boolean isUsingColors() {
	return getRenderer().isUsingColors();
    }

    public void setUsingColors(boolean colored) {
	if (colored != isUsingColors()) {
	    getRenderer().setUsingColors(colored);
	    tree.revalidate();
	    tree.repaint();
	}
    }

    public void modelUpdated(boolean selectionRemoved) {
	if (selectionRemoved) {
	    tree.clearSelection();
	}
	((MemberModel)tree.getModel()).updateRoots();
	// changeSelection();
    }

    class MemberTreeSelectionListener implements TreeSelectionListener {

	/** 
	    Used to indicated an internal redirection of a model element
	    that shall be displayed by the tree but not propagated to the 
	    model.
	    With this trick we do not have to remove / re-add the
	    listener to the tree each time.
	*/
	ModelElement redirected;

	public void valueChanged(TreeSelectionEvent e) {
	    TreePath path = tree.getSelectionPath();
	    if (path != null) {
		Object leaf = path.getLastPathComponent();
		if (leaf instanceof ModelElement && leaf != redirected) {
		    model.setSelectedElement((ModelElement)leaf);
		}
	    }
	}
    }

    MemberTreeSelectionListener selectionListener =
	new MemberTreeSelectionListener();

    ChangeListener changeListener = new ChangeListener() {
	    public void stateChanged(ChangeEvent e) {
		changeSelection();
	    }
	};

    private void changeSelection() {
	ModelElement e = model == null ? null : model.getSelectedElement();
	if (e instanceof ProgramModelElement) {
	    selectElement((ProgramModelElement)e, false, true);
	}  else if (e instanceof ProgramElement) {
	    ProgramModelElement pme = RecoderUtils.getAssociatedProgramModelElement((ProgramElement)e);
	    selectionListener.redirected = pme;
	    selectElement(pme, false, true);
	    selectionListener.redirected = null;	    
	} else {
	    tree.clearSelection();
	}
    }

    // expands and scrolls to the element
    public void selectElement(ProgramModelElement p, boolean autoExpand, boolean autoScroll) {
	TreePath tpath = createPath(((MemberModel)tree.getModel()).getRoot(), p);
	tree.setSelectionPath(tpath);
	if (autoExpand) {
	    tree.expandPath(tpath);
	}
	if (autoScroll) {
	    tree.scrollPathToVisible(tpath);
	}
    }


    protected static TreePath createPath(Object root, ProgramModelElement node) {
	List path = new ArrayList();
	do {
	    path.add(node);	    
	    node = RecoderUtils.getContainer(node);
	} while (node != null);
	path.add(root);
	Object[] elements = new Object[path.size()];
	for (int i = 0, s = elements.length; i < s; i += 1) {
	    elements[i] = path.get(s - i - 1);
	}
	return new TreePath(elements);
    }

    /**
       Member tree model representing the package - class - member hierarchy.
    */
    public static class MemberModel implements TreeModel {

	private NameInfo nameInfo;
	
	private Vector treeModelListeners = new Vector();
	
	private String root = "System";
	
	/**
	   Contains mapping <Object, ProgramModelElement[]>, e.g.
	   root -> packages,
	   packages -> class types,
	   ClassTypeContainer -> members
	 */
	private Map querycache;
	
	
	public MemberModel(NameInfo nameInfo) {
	    this.nameInfo = nameInfo;
	    querycache = new HashMap();
	}

	public void updateRoots() {
	    querycache.clear();
	    if (!treeModelListeners.isEmpty()) {
		Enumeration enum2 = treeModelListeners.elements();
		TreeModelEvent event = new TreeModelEvent(this, new TreePath(root));
		while (enum2.hasMoreElements()) {
		    ((TreeModelListener)enum2.nextElement()).treeStructureChanged(event);
		}
	    }
	}
	
	final static Order BY_NAME = new Order.Lexical() {
		protected String toString(Object x) {
		    return ((NamedModelElement)x).getName();
		}
	    };

	final static ProgramModelElement[] LEAF_NODE =
	    new ProgramModelElement[0];

	private ProgramModelElement[] getChildren(Object parent) {
	    ProgramModelElement[] res =
		(ProgramModelElement[])querycache.get(parent);
	    if (res == null) {
		res = computeChildren(parent);
		querycache.put(parent, res);
	    }
	    return res;
	}

	private ProgramModelElement[] computeChildren(Object parent) {
	    ProgramModelElement[] res;
	    int count = 0;
	    if (parent == root) {
		res = nameInfo.getPackages().toArray(new ProgramModelElement[nameInfo.getPackages().size()]);
		Sorting.heapSort(res, BY_NAME);
	    } else if (parent instanceof ClassTypeContainer) {
		ProgramModelElement[] types = null;
		ProgramModelElement[] cons = null;
		ProgramModelElement[] fields = null;
		ProgramModelElement[] methods = null;
		List<? extends ProgramModelElement> mlist = null;
		mlist = ((ClassTypeContainer)parent).getTypes();
		if (mlist != null) {
		    count += mlist.size();
		    types = mlist.toArray(new ProgramModelElement[mlist.size()]);
		    Sorting.heapSort(types, BY_NAME);
		}
		if (parent instanceof ClassType) {
		    ClassType ct = (ClassType)parent;
		    mlist = ct.getFields();
		    if (mlist != null) {
			fields = mlist.toArray(new ProgramModelElement[mlist.size()]);
			count += mlist.size();
			Sorting.heapSort(fields, BY_NAME);
		    }
		    mlist = ct.getConstructors();
		    if (mlist != null) {
			cons = mlist.toArray(new ProgramModelElement[mlist.size()]);
			count += mlist.size();
			Sorting.heapSort(cons, BY_NAME);
		    }
		    mlist = ct.getMethods();
		    if (mlist != null) {
			methods = mlist.toArray(new ProgramModelElement[mlist.size()]);
			count += mlist.size();
			Sorting.heapSort(methods, BY_NAME);
		    }
		}
		if (count == 0) {
		    res = LEAF_NODE;
		} else {
		    res = new ProgramModelElement[count];
		    int i = 0;
		    if (types != null) {
			System.arraycopy(types, 0, res, i, types.length);
			i += types.length;
		    }
		    if (fields != null) {
			System.arraycopy(fields, 0, res, i, fields.length);
			i += fields.length;
		    }
		    if (cons != null) {
			System.arraycopy(cons, 0, res, i, cons.length);
			i += cons.length;
		    }
		    if (methods != null) {
			System.arraycopy(methods, 0, res, i, methods.length);
			i += methods.length;
		    }
		}
	    } else {
		res = LEAF_NODE;
	    }
	    return res;
	}
	
	public void addTreeModelListener(TreeModelListener l) {
	    treeModelListeners.addElement(l);
	}    
	
	public void removeTreeModelListener(TreeModelListener l) {
	    treeModelListeners.removeElement(l);
	}
	
	public Object getRoot() {
	    return root;
	}
	
	public int getChildCount(Object parent) {
	    return getChildren(parent).length;
	}

	
	public int getIndexOfChild(Object parent, Object child) {
	    ProgramModelElement[] children = getChildren(parent);
	    // searching backwards is okay here, children occur at most once
	    for (int i = children.length - 1; i >= 0; i -= 1) {
		if (children[i] == child) {
		    return i;
		}					  
	    }
	    return -1;
	}
	
	public Object getChild(Object parent, int index) {
	    return getChildren(parent)[index];
	}
	
	public boolean isLeaf(Object node) {
	    return getChildren(node) == LEAF_NODE;
	}
	
	public void valueForPathChanged(TreePath path, Object newValue) {}
    }


    public static class MemberRenderer extends DefaultTreeCellRenderer {

	private boolean useColors = true;

	public boolean isUsingColors() {
	    return useColors;
	}

	public void setUsingColors(boolean colored) {
	    useColors = colored;	    
	}

	// StringBuffer buffer = new StringBuffer();

	public Component getTreeCellRendererComponent
	    (JTree tree, Object value, boolean sel, boolean expanded, 
	     boolean leaf, int row, boolean hasFocus) {	
	    super.getTreeCellRendererComponent
		(tree, value, sel, expanded, leaf, row, hasFocus);
	    setIcon(null);
	    //	    buffer.setLength(0);
	    if (value instanceof Member) {
		Member mb = (Member)value;
		if (mb instanceof Method) {
		    Method me = (Method)mb;
		    if (value instanceof Constructor) {
			if (me.isPublic()) {
			    setIcon(Resources.PUBLIC_CONSTRUCTOR_ICON);
			} else if (me.isProtected()) {
			    setIcon(Resources.PROTECTED_CONSTRUCTOR_ICON);
			} else if (me.isPrivate()) {
			    setIcon(Resources.PRIVATE_CONSTRUCTOR_ICON);
			} else {
			    setIcon(Resources.PACKAGE_CONSTRUCTOR_ICON);
			}
		    } else {
			if (me.isAbstract()) {
			    if (me.isPublic()) {
				setIcon(Resources.ABSTRACT_PUBLIC_METHOD_ICON);
			    } else if (me.isProtected()) {
				setIcon(Resources.ABSTRACT_PROTECTED_METHOD_ICON);
			    } else {
				setIcon(Resources.ABSTRACT_PACKAGE_METHOD_ICON);
			    }
			} else if (me.isPublic()) {
			    if (me.isStatic()) {
				if (me.isFinal()) {
				    setIcon(Resources.PUBLIC_FINAL_STATIC_METHOD_ICON);
				} else {
				    setIcon(Resources.PUBLIC_STATIC_METHOD_ICON);
				}
			    } else {
				if (me.isFinal()) {
				    setIcon(Resources.PUBLIC_FINAL_METHOD_ICON);
				} else {
				    setIcon(Resources.PUBLIC_METHOD_ICON);
				}
			    }
			} else if (mb.isProtected()) {
			    if (me.isStatic()) {
				if (me.isFinal()) {
				    setIcon(Resources.PROTECTED_FINAL_STATIC_METHOD_ICON);
				} else {
				    setIcon(Resources.PROTECTED_STATIC_METHOD_ICON);
				}
			    } else {
				if (me.isFinal()) {
				    setIcon(Resources.PROTECTED_FINAL_METHOD_ICON);
				} else {
				    setIcon(Resources.PROTECTED_METHOD_ICON);
				}
			    }
			} else if (mb.isPrivate()) {
			    if (me.isStatic()) {
				if (me.isFinal()) {
				    setIcon(Resources.PRIVATE_FINAL_STATIC_METHOD_ICON);
				} else {
				    setIcon(Resources.PRIVATE_STATIC_METHOD_ICON);
				}
			    } else {
				if (me.isFinal()) {
				    setIcon(Resources.PRIVATE_FINAL_METHOD_ICON);
				} else {
				    setIcon(Resources.PRIVATE_METHOD_ICON);
				}
			    }
			} else {
			    if (me.isStatic()) {
				if (me.isFinal()) {
				    setIcon(Resources.PACKAGE_FINAL_STATIC_METHOD_ICON);
				} else {
				    setIcon(Resources.PACKAGE_STATIC_METHOD_ICON);
				}
			    } else {
				if (me.isFinal()) {
				    setIcon(Resources.PACKAGE_FINAL_METHOD_ICON);
				} else {
				    setIcon(Resources.PACKAGE_METHOD_ICON);
				}
			    }
			}
		    }
		} else if (mb instanceof Field) {
		    Field f = (Field)mb;
		    if (f.isPublic()) {
			if (f.isStatic()) {
			    if (f.isFinal()) {
				setIcon(Resources.PUBLIC_FINAL_STATIC_FIELD_ICON);
			    } else {
				setIcon(Resources.PUBLIC_STATIC_FIELD_ICON);
			    }
			} else {
			    if (f.isFinal()) {
				setIcon(Resources.PUBLIC_FINAL_FIELD_ICON);
			    } else {
				setIcon(Resources.PUBLIC_FIELD_ICON);
			    }
			}
		    } else if (mb.isProtected()) {
			if (f.isStatic()) {
			    if (f.isFinal()) {
				setIcon(Resources.PROTECTED_FINAL_STATIC_FIELD_ICON);
			    } else {
				setIcon(Resources.PROTECTED_STATIC_FIELD_ICON);
			    }
			} else {
			    if (f.isFinal()) {
				setIcon(Resources.PROTECTED_FINAL_FIELD_ICON);
			    } else {
				setIcon(Resources.PROTECTED_FIELD_ICON);
			    }
			}
		    } else if (mb.isPrivate()) {
			if (f.isStatic()) {
			    if (f.isFinal()) {
				setIcon(Resources.PRIVATE_FINAL_STATIC_FIELD_ICON);
			    } else {
				setIcon(Resources.PRIVATE_STATIC_FIELD_ICON);
			    }
			} else {
			    if (f.isFinal()) {
				setIcon(Resources.PRIVATE_FINAL_FIELD_ICON);
			    } else {
				setIcon(Resources.PRIVATE_FIELD_ICON);
			    }
			}
		    } else {
			if (f.isStatic()) {
			    if (f.isFinal()) {
				setIcon(Resources.PACKAGE_FINAL_STATIC_FIELD_ICON);
			    } else {
				setIcon(Resources.PACKAGE_STATIC_FIELD_ICON);
			    }
			} else {
			    if (f.isFinal()) {
				setIcon(Resources.PACKAGE_FINAL_FIELD_ICON);
			    } else {
				setIcon(Resources.PACKAGE_FIELD_ICON);
			    }
			}
		    }
		} else if (mb instanceof ClassType) {
		    ClassType ct = (ClassType)mb;
		    if (ct.isAbstract()) {
			if (ct.isStatic()) {
			    if (ct.isPublic()) {
				setIcon(Resources.ABSTRACT_PUBLIC_STATIC_CLASS_ICON);
			    } else if (ct.isProtected()) {
				setIcon(Resources.ABSTRACT_PROTECTED_STATIC_CLASS_ICON);
			    } else {
				setIcon(Resources.ABSTRACT_PACKAGE_STATIC_CLASS_ICON);
			    }			    
			} else {
			    if (ct.isPublic()) {
				setIcon(Resources.ABSTRACT_PUBLIC_CLASS_ICON);
			    } else {
				setIcon(Resources.ABSTRACT_PACKAGE_CLASS_ICON);
			    }
			}
		    } else if (ct.isPublic()) {
			if (ct.isStatic()) {
			    if (ct.isFinal()) {
				setIcon(Resources.PUBLIC_FINAL_STATIC_CLASS_ICON);
			    } else {
				setIcon(Resources.PUBLIC_STATIC_CLASS_ICON);
			    }
			} else {
			    if (ct.isFinal()) {
				setIcon(Resources.PUBLIC_FINAL_CLASS_ICON);
			    } else {
				setIcon(Resources.PUBLIC_CLASS_ICON);
			    }
			}
		    } else if (mb.isProtected()) {
			if (ct.isStatic()) {
			    if (ct.isFinal()) {
				setIcon(Resources.PROTECTED_FINAL_STATIC_CLASS_ICON);
			    } else {
				setIcon(Resources.PROTECTED_STATIC_CLASS_ICON);
			    }
			} else {
			    if (ct.isFinal()) {
				setIcon(Resources.PROTECTED_FINAL_CLASS_ICON);
			    } else {
				setIcon(Resources.PROTECTED_CLASS_ICON);
			    }
			}
		    } else if (mb.isPrivate()) {
			if (ct.isStatic()) {
			    if (ct.isFinal()) {
				setIcon(Resources.PRIVATE_FINAL_STATIC_CLASS_ICON);
			    } else {
				setIcon(Resources.PRIVATE_STATIC_CLASS_ICON);
			    }
			} else {
			    if (ct.isFinal()) {
				setIcon(Resources.PRIVATE_FINAL_CLASS_ICON);
			    } else {
				setIcon(Resources.PRIVATE_CLASS_ICON);
			    }
			}
		    } else {
			if (ct.isStatic()) {
			    if (ct.isFinal()) {
				setIcon(Resources.PACKAGE_FINAL_STATIC_CLASS_ICON);
			    } else {
				setIcon(Resources.PACKAGE_STATIC_CLASS_ICON);
			    }
			} else {
			    if (ct.isFinal()) {
				setIcon(Resources.PACKAGE_FINAL_CLASS_ICON);
			    } else {
				setIcon(Resources.PACKAGE_CLASS_ICON);
			    }
			}
		    }
		}
		setText(Format.toString("%m", mb));
		if (useColors) {
		    if (value instanceof Method) {
			if (value instanceof Constructor) {
			    setForeground(Resources.CONSTRUCTOR_COLOR);
			} else {
			    setForeground(Resources.METHOD_COLOR);
			}
		    } else if (value instanceof Field) {
			setForeground(Resources.VARIABLE_COLOR);
		    } else if (value instanceof ClassType) {
			setForeground(Resources.TYPE_COLOR);
		    }
		}
	    } else if (value instanceof Package) {
		setIcon(Resources.PACKAGE_ICON);
		String name = ((Package)value).getFullName();
		if (name.length() == 0) {
		    setText("(Default Package)");
		} else {
		    setText(name);
		}
		if (useColors) {
		    setForeground(Resources.PACKAGE_COLOR);
		}
	    }
	    // setText(buffer.toString());
	    return this;
	}
    }

}

