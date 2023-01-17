package sourcerer.view;

import java.awt.BorderLayout;
import java.awt.Color;
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
import recoder.ServiceConfiguration;
import recoder.abstraction.Package;
import recoder.convenience.Naming;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.Declaration;
import recoder.java.NamedProgramElement;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.Reference;
import recoder.java.TerminalProgramElement;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.java.reference.ConstructorReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.PackageReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.kit.UnitKit;
import recoder.service.NameInfo;
import recoder.util.Order;
import sourcerer.Resources;
import sourcerer.SelectionModel;
import sourcerer.util.RecoderUtils;

/**
*/
public class SyntaxView extends JPanel implements SelectionView {

    protected SelectionModel model;

    boolean showNames = true;
    boolean useColors = true;

    boolean showSyntaxTrees = true;

    protected JTree tree;

    public SyntaxView(final SelectionModel model, ServiceConfiguration sc) {
	super(new BorderLayout());
	setName("Syntax Forest");
	tree = new JTree(new SyntaxModel(sc));
	tree.setLargeModel(true); // optimizing; all cells have equal height
	tree.setCellRenderer(new SyntaxRenderer());
	tree.setRootVisible(false);
	tree.setShowsRootHandles(true);
	tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
	tree.putClientProperty("JTree.lineStyle", "Angled");
	tree.addTreeSelectionListener(selectionListener);
	add(new JScrollPane(tree));
	setModel(model);
    }

    public SelectionModel getModel() {
	return model;
    }

    public JTree getTree() {
	return tree;
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

    public void modelUpdated(boolean selectionRemoved) {
	if (selectionRemoved) {
	    tree.clearSelection();
	}
	((SyntaxModel)tree.getModel()).update();
    }

    public boolean isShowingSyntaxTrees() {
	return showSyntaxTrees;
    }

    public void setShowingSyntaxTrees(boolean show) {
	if (show != showSyntaxTrees) {
	    showSyntaxTrees = show;
	    ((SyntaxModel)tree.getModel()).update();
	    changeSelection();
	}
    }

    public boolean isShowingNames() {
	return showNames;
    }

    public void setShowingNames(boolean show) {
	if (show != showNames) {
	    showNames = show;
	    tree.revalidate();
	    tree.repaint();
	}
    }

    public boolean isUsingColors() {
	return useColors;
    }

    public void setUsingColors(boolean colored) {
	if (colored != useColors) {
	    useColors = colored;
	    tree.revalidate();
	    tree.repaint();
	}
    }

    SyntaxRenderer getRenderer() {
	return (SyntaxRenderer)tree.getCellRenderer();
    }

    class SyntaxTreeSelectionListener implements TreeSelectionListener {

	/** 
	    Used to indicated an internal redirection of a model
	    element that shall be displayed by the tree but not
	    propagated to the model.  With this trick we do not have
	    to remove / re-add the listener to the tree each time.
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

    SyntaxTreeSelectionListener selectionListener = 
	new SyntaxTreeSelectionListener();

    ChangeListener changeListener = new ChangeListener() {
	    public void stateChanged(ChangeEvent e) {
		changeSelection();
	    }
	};


    private void changeSelection() {
	ModelElement e = model == null ? null : model.getSelectedElement();
	if (e instanceof Package) {
	    selectElement(e, false, true);
	} else if (e instanceof ProgramElement) {
	    if (showSyntaxTrees || e instanceof CompilationUnit) {
		selectElement(e, false, true);
	    } else {
		e = UnitKit.getCompilationUnit((ProgramElement) e);
		selectionListener.redirected = e;
		selectElement(e, false, true);
		selectionListener.redirected = null;
	    }
	} else {
	    tree.clearSelection();
	}
    }

    // expands and scrolls to the element
    public void selectElement(ModelElement p, boolean autoExpand, boolean autoScroll) {
	TreePath tpath = ((SyntaxModel)tree.getModel()).createPath(p);
	tree.setSelectionPath(tpath);
	if (autoExpand) {
	    tree.expandPath(tpath);
	}
	if (autoScroll) {
	    tree.scrollPathToVisible(tpath);
	}
    }

    final static Order UNIT_ORDER = new Order.Lexical() {
	    protected String toString(Object x) {
		return RecoderUtils.getShortName((CompilationUnit)x);
	    }
	};
    
    final static Order PACKAGE_SHORT_ORDER = new Order.Lexical() {
	    protected String toString(Object x) {
		return RecoderUtils.getShortName((Package)x);
	    }
	    };
	
    
    /**
       Tree model representing the directory - unit hierarchy and
       additionally, the syntax tree.
    */
    public class SyntaxModel implements TreeModel {

	private Vector treeModelListeners = new Vector();
	
	private String root = "System";

	private NameInfo nameInfo;
	private SourceFileRepository sfr;
		
	/**
	   Contains mapping <Object, Object[]>, e.g.
	   root -> packages,
	   packages -> packages | units
	 */
	private Map cache;

	public SyntaxModel(ServiceConfiguration config) {
	    this.nameInfo = config.getNameInfo();
	    this.sfr = config.getSourceFileRepository();
	    cache = new HashMap();
	    computeCache();
	}
	
	public void update() {
	    computeCache();
	    if (!treeModelListeners.isEmpty()) {
		Enumeration enum2 = treeModelListeners.elements();
		TreeModelEvent event = new TreeModelEvent(this, new TreePath(root));
		while (enum2.hasMoreElements()) {
		    ((TreeModelListener)enum2.nextElement()).treeStructureChanged(event);
		}
	    }
	}
	
	private void computeCache() {
	    cache.clear();
	    List<CompilationUnit> units = sfr.getCompilationUnits();
	    for (int i = units.size() - 1; i >= 0; i -= 1) {
		CompilationUnit cu = units.get(i);
		String pname = Naming.getPackageName(cu);
		Package p = nameInfo.getPackage(pname);
		List<ModelElement> list = (List<ModelElement>)cache.get(p);
		if (list == null) {
		    list = new ArrayList<ModelElement>();
		    cache.put(p, list);
		}
		// insert to proper position (insert from end)
		for (int j = list.size() - 1; true; j -= 1) {
		    if (j < 0) {
			list.add(0, cu);
			break;
		    }
		    ModelElement m = list.get(j);
		    if ((m instanceof Package) ||
			UNIT_ORDER.lessOrEquals(m, cu)) {
			list.add(j + 1, cu);
			break;
		    }
		}
		int dot = pname.lastIndexOf('.');
		while (dot >= 0) {
		    pname = pname.substring(0, dot);
		    Package q = nameInfo.getPackage(pname);
		    list = (List<ModelElement>)cache.get(q);
		    if (list == null) {
			list = new ArrayList<ModelElement>();
			cache.put(q, list);
		    }
		    // insert to proper position (insert from beginning)
		    for (int j = 0, s = list.size(); true; j += 1) {
			if (j >= s) {
			    list.add(p);
			    break;
			}
			ModelElement m = list.get(j);
			if (m == p) {
			    // only insert once
			    break;
			}
			if ((m instanceof Package) &&
			    PACKAGE_SHORT_ORDER.greaterOrEquals(m, p)) {
			    list.add(j, p);
			    break;
			}
		    }
		    // Debug.log(Format.toString("%c %N %u", list));  
		    p = q;
		    dot = pname.lastIndexOf('.');
		}
		list = (List<ModelElement>)cache.get(root);
		if (list == null) {
		    list = new ArrayList<ModelElement>();
		    cache.put(root, list);
		}
		for (int j = 0, s = list.size(); true; j += 1) {
		    if (j >= s) {
			list.add(p);
			break;
		    }
		    ModelElement m = list.get(j);
		    if (m == p) {
			// only insert once
			break;
		    }
		    if ((m instanceof Package) &&
			PACKAGE_SHORT_ORDER.greaterOrEquals(m, p)) {
			list.add(j, p);
			break;
		    }
		}		
	    }	    	    
	}

	protected TreePath createPath(ModelElement node) {
	    List path = new ArrayList();
	    do {
		path.add(node);
		if (node instanceof Package) {
		    String name = ((Package)node).getName();
		    int dot = name.lastIndexOf('.');
		    if (dot >= 0) {
			name = name.substring(0, dot);
			node = nameInfo.getPackage(name);
		    } else {
			node = null;
		    }
		} else if (node instanceof ProgramElement) {
		    if (node instanceof CompilationUnit) {
			node = nameInfo.getPackage(Naming.getPackageName((CompilationUnit)node));
		    } else {
			node = ((ProgramElement)node).getASTParent();
		    }    
		}
	    } while (node != null);
	    path.add(root);
	    Object[] elements = new Object[path.size()];
	    for (int i = 0, s = elements.length; i < s; i += 1) {
		elements[i] = path.get(s - i - 1);
	    }
	    return new TreePath(elements);
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
	    if (parent instanceof ProgramElement) {
		if (showSyntaxTrees && 
		    (parent instanceof NonTerminalProgramElement)) {
		    return ((NonTerminalProgramElement)parent).getChildCount();
		} else {
		    return 0;
		}		
	    }
	    List<ModelElement> children = (List<ModelElement>)cache.get(parent);
	    return (children == null) ? 0 : children.size();
	}

	
	public int getIndexOfChild(Object parent, Object child) {
	    if (parent instanceof ProgramElement) {
		if (showSyntaxTrees && (parent instanceof NonTerminalProgramElement)) {		
		    return ((NonTerminalProgramElement)parent).getIndexOfChild((ProgramElement)child);
		} else {
		    return -1;
		}
	    }		
	    List<ModelElement> children = (List<ModelElement>)cache.get(parent);
	    return (children == null) ? -1 : children.indexOf(child);
	}
	
	public Object getChild(Object parent, int index) {
	    if (parent instanceof ProgramElement) {
		if (showSyntaxTrees && (parent instanceof NonTerminalProgramElement)) {
		    return ((NonTerminalProgramElement)parent).getChildAt(index);
		} else {
		    return null;
		}
	    }
	    List<ModelElement> children = (List<ModelElement>)cache.get(parent);
	    return (children == null) ? null : children.get(index);
	}
	
	public boolean isLeaf(Object node) {
	    return showSyntaxTrees 
		? (node instanceof TerminalProgramElement)
		: (node instanceof CompilationUnit);
	}
	
	public void valueForPathChanged(TreePath path, Object newValue) {}
    }


    class SyntaxRenderer extends DefaultTreeCellRenderer {

	public Component getTreeCellRendererComponent
	    (JTree tree, Object value, boolean sel, boolean expanded, 
	     boolean leaf, int row, boolean hasFocus) {	
	    super.getTreeCellRendererComponent
		(tree, value, sel, expanded, leaf, row, hasFocus);
	    if (value instanceof CompilationUnit) {
		if (useColors) {
		    this.setForeground(Resources.COMPILATION_UNIT_COLOR);
		}
		String name = RecoderUtils.getShortName((CompilationUnit)value);
		if (showSyntaxTrees) {
		    setText("CompilationUnit \"" + name + "\"");
		} else {
		    setText(name);
		}
	    } else if (value instanceof Package) {
		if (useColors) {
		    this.setForeground(Resources.PACKAGE_COLOR);
		}
		String name = RecoderUtils.getShortName((Package)value);
		if (name.length() == 0) {
		    name = "(Default Package)";
		}
		setText(name);
	    } else {
		String text = value.getClass().getName();
		text = text.substring(text.lastIndexOf('.') + 1);
		if (showNames) {
		    if (value instanceof NamedProgramElement) {
			text += " \"" + ((NamedProgramElement)value).getName() + "\"";
		    }
		}
		setText(text);
		if (useColors) {
		    if (value instanceof Reference) {
			if (value instanceof TypeReference) {
			    this.setForeground(Resources.TYPE_REFERENCE_COLOR);
			} else if (value instanceof VariableReference) {
			    this.setForeground(Resources.VARIABLE_REFERENCE_COLOR);
			} else if (value instanceof ConstructorReference) {
			    this.setForeground(Resources.CONSTRUCTOR_REFERENCE_COLOR);
			} else if (value instanceof MethodReference) {
			    this.setForeground(Resources.METHOD_REFERENCE_COLOR);
			} else if (value instanceof PackageReference) {
			    this.setForeground(Resources.PACKAGE_REFERENCE_COLOR);
			} else {
			    this.setForeground(Color.black);
			}
		    } else if (value instanceof Declaration) {
			if (value instanceof VariableSpecification) {
			    this.setForeground(Resources.VARIABLE_COLOR);
			} else if (value instanceof ConstructorDeclaration) {
			    this.setForeground(Resources.CONSTRUCTOR_COLOR);
			} else if (value instanceof MethodDeclaration) {
			    this.setForeground(Resources.METHOD_COLOR);
			} else if (value instanceof TypeDeclaration) {
			    this.setForeground(Resources.TYPE_COLOR);
			} else {
			    this.setForeground(Color.black);
			}
		    } else {
			this.setForeground(Color.black);
		    }
		} else {
		    this.setForeground(Color.black);
		}
	    }
	    setIcon(null);
	    return this;
	}
    }
}
