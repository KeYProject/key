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

import java.awt.Color;
import java.awt.Component;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Vector;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.MutableTreeNode;
import javax.swing.tree.TreeModel;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.recoderext.ClassInitializeMethodBuilder;
import de.uka.ilkd.key.jml.*;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.IteratorOfProgramMethod;
import de.uka.ilkd.key.logic.op.ListOfProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.*;


public class JMLSpecBrowser extends JDialog {

    /** the package hierarchy as a tree */
    private JTree packageHierarchy;

    private JList methodList; 
    private JList poList;

    private JCheckBox allInv;
    private JCheckBox invPost;

    private Implementation2SpecMap ism;


    /** true if the JMLSpecBrowser was invoked by Main and we already have
     * a proofenvironment for the javaModel we are dealing with.
     */
    private boolean envMode = true;

    private KeYMediator mediator;
    private Services services;

    private JMLProofOblInput poi = null;

    private String javaPath = "";

    private Object[] emptyArray = new Object[0];

    private TreeModel treeModel;

    private static HashMap ism2browser = new HashMap();

    private boolean inheritedMethods = false;

    //the selected class
    private KeYJavaType classType = null;

    private JMLSpecBrowser(KeYMediator mediator) {  
	super(new JFrame(), "JML Specification Browser", true);
       	this.services = mediator.getServices();
	ism = services.getImplementation2SpecMap();
	this.mediator = mediator;
	this.javaPath = mediator.getProof().env().getJavaModel().getModelDir();
	buildTreeModel();
	layoutJMLSpecBrowser();
	pack();
	setLocation(70, 70);
	setVisible(true);
    }

    public JMLSpecBrowser(Services services, String javaPath) {  
	super(new JFrame(), "JML Specification Browser", true);
       	this.services = services;
	ism = services.getImplementation2SpecMap();
	this.javaPath = javaPath;
	envMode = false;
	buildTreeModel();
	layoutJMLSpecBrowser();
	pack();
	setLocation(70, 70);
	setVisible(true);
	ism2browser.put(services.getImplementation2SpecMap(), this);
    }

    public static JMLSpecBrowser getJMLSpecBrowser(KeYMediator mediator){
	JMLSpecBrowser browser = (JMLSpecBrowser)ism2browser.
	  get(mediator.getServices().getImplementation2SpecMap());
        if(browser == null) {
	   browser = new JMLSpecBrowser(mediator);
	   ism2browser.put(mediator.getServices().
			    getImplementation2SpecMap(), 
			    browser);
	}
	browser.envMode = true;
	browser.mediator = mediator;
	browser.setModal(true);
	browser.setVisible(true);
	return browser;
    }

    /**
     * builds a TreeModel from the package structure of the Java model.
     */
    private void buildTreeModel(){
	JavaInfo ji = services.getJavaInfo();
	HashMap package2Node = new HashMap();
	DefaultMutableTreeNode root = new DefaultMutableTreeNode("");
//	ism.checkPurity();

	Iterator it = ism.getAllClasses().iterator();
	while(it.hasNext()){
	    KeYJavaType kjt = (KeYJavaType) it.next();
	    String name = ji.getFullName(kjt);
	    if(name.lastIndexOf(".") != -1){
		DefaultMutableTreeNode parent = 
		    treeHelper(name.substring(0, name.lastIndexOf(".")),
			       package2Node, root);
		parent.add(new DefaultMutableTreeNode(kjt){
		    public String toString(){
			final String sortName = 
                            ((KeYJavaType) userObject).getSort().toString();
			return sortName.substring(sortName.lastIndexOf(".")+1); 
		    }
		});
	    }else{
		root.add(new DefaultMutableTreeNode(kjt){
			public String toString(){
			    return ((KeYJavaType) userObject).getSort().
				toString();
			}
		});
	    }
	}
	sortTree(root);
	if(root.getChildCount() == 1){
	    treeModel = new DefaultTreeModel(root.getFirstChild());
	}else{
	    treeModel = new DefaultTreeModel(root);
	}
	packageHierarchy = new JTree(treeModel);
	packageHierarchy.addTreeSelectionListener(
	    new GUIPackageTreeSelectionListener());
    }

    private void sortTree(DefaultMutableTreeNode root){
	for(int i = 0; i<root.getChildCount(); i++){
	    sortTree((DefaultMutableTreeNode) root.getChildAt(i));
	}
	boolean changed = true;
	while(changed){
	    changed = false;
	    for(int i = 0; i<root.getChildCount()-1; i++){
		if(root.getChildAt(i).toString().compareTo(
		   root.getChildAt(i+1).toString()) > 0){
		    changed = true;
		    root.insert((MutableTreeNode)root.getChildAt(i+1), i);
		}
	    }
	}
    }

    private DefaultMutableTreeNode treeHelper(String pname, HashMap p2n, 
					      DefaultMutableTreeNode root){
	if(p2n.get(pname) != null){
	    return (DefaultMutableTreeNode) p2n.get(pname);
	}else{
	    final int dot = pname.lastIndexOf(".");
	    DefaultMutableTreeNode node = 
		new DefaultMutableTreeNode(pname){
		    public String toString(){
			return userObject.toString().substring(dot+1);
		    }
		};
	    p2n.put(pname, node);
	    if(dot != -1){
		DefaultMutableTreeNode parent = 
		    treeHelper(pname.substring(0, dot),
			       p2n, root);
		parent.add(node);
	    }else{
		root.add(node);
	    }
	    return node;
	}
    }

    /** layout */
    protected void layoutJMLSpecBrowser() {
	JScrollPane classListScroll = new
	    JScrollPane(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, 
			JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
	classListScroll.getViewport().setView(packageHierarchy);
	classListScroll.setBorder(new TitledBorder("Classes"));

	methodList = new JList();
	JPanel methodPanel = new JPanel();
	methodPanel.setLayout(new BoxLayout(methodPanel, BoxLayout.PAGE_AXIS));
	final JButton hide = 
	    new JButton(inheritedMethods ? "Hide Inherited Methods" :
			"Show Inherited Methods");
	hide.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    inheritedMethods = !inheritedMethods;
		    hide.setText(inheritedMethods ? "Hide Inherited Methods" :
				 "Show Inherited Methods");
		    updateMethodList(classType);
		}

	    });
	methodList.addListSelectionListener(new ListSelectionListener() {
		public void valueChanged(ListSelectionEvent e) {
		    setPOList();				
		}});
	methodList.setCellRenderer(new DefaultListCellRenderer(){
		public Component getListCellRendererComponent(
		    JList list,
		    Object value,
		    int index,
		    boolean isSelected,
		    boolean cellHasFocus)
		    {
			if(value != null){
			    ProgramMethod pm = (ProgramMethod) value;
			    MethodDeclaration md = pm.getMethodDeclaration();
			    String params = md.getParameters().toString();
			    setText((md.getTypeReference() == null ? "void" : 
					md.getTypeReference().getName())+
				    " "+md.getFullName()+"("+
				    params.substring(1,params.length()-1)+")");
			    if (isSelected) {
				setBackground(list.getSelectionBackground());
				setForeground(list.getSelectionForeground());
			    }
			    else {
				setBackground(list.getBackground());
				setForeground(list.getForeground());
			    }
			    setEnabled(list.isEnabled());
			    setFont(list.getFont());
			    setOpaque(true);
			}
			return this;
		    }
		    });
	JScrollPane methodListScroll = new
	    JScrollPane(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, 
			JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
	methodListScroll.getViewport().setView(methodList);
	methodListScroll.setBorder(new TitledBorder("Methods"));

	poList = new JList();
	
	poList.setCellRenderer(new TextAreaRenderer());
	JScrollPane poListScroll = new
	    JScrollPane(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, 
			JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
	poListScroll.getViewport().setView(poList);
	poListScroll.setBorder(new TitledBorder("Proof Obligations"));

	JPanel buttonPanel = new JPanel();

	JPanel optionPanel = new JPanel();
	optionPanel.setLayout(new BoxLayout(optionPanel, BoxLayout.Y_AXIS));
	buttonPanel.add(optionPanel);

	allInv = new JCheckBox("Use all applicable invariants");
	allInv.setToolTipText("<html><pre>"+
			      "If selected, the POs change to that effect,<br>"+
			      "that every invariant of every class is added\n"+
			      "to the precondition in the case of method\n"+
			      "specification POs, or to the pre- and\n"+
			      "postcondition in the case of invariant POs.\n "+
			      "  This changes the semantics of the invariant\n"+
			      "PO to that extend that it now expresses that\n"+
			      "the method preserves every invariant of every"+
			      "\nexisting object and type.\n"+
			      "  The effect on method spec POs is that they\n"+
			      "are then reflecting the fact that a method\n"+
			      "can assume all invariants of every existing\n"+
			      "object and type to hold in its prestate.\n"+
			      "Assuming all invariants to hold in the\n"+
			      "prestate of a certain method is often not\n"+
			      "necessary when proving its specification!"+
			      "</pre>");
	optionPanel.add(allInv);
	allInv.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    setPOList();
		}
	    });

	invPost = new JCheckBox("Add invariants to postcondition");
	invPost.setToolTipText("<html><pre>"+
			       "If selected the history constraints and\n"+
			       "invariants of the current class are added\n"+
			       "to the postcondition of the method speccase PO\n"+
			       "(this is the case if \"Use all applicable\n"+
			       "invariants\" is not selected otherwise also\n"+
			       "the invariants of every other class are added)"+
			       "</pre>");
	optionPanel.add(invPost);

	JButton lo = 
	    new JButton("Load Proof Obligation");
	lo.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    if(poList.getSelectedValue() == null){
			JOptionPane.showMessageDialog(
			    null, "Please select the PO you wish to load!",
			    "Which Proof Obligation?", 
			    JOptionPane.ERROR_MESSAGE);
		    }else{
			createProofObl();
			setVisible(false);
			setModal(false);
//			dispose();
		    }
		}
	    });
	buttonPanel.add(lo);
	JButton cancel = new JButton("Cancel");
	cancel.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    setVisible(false);
		    setModal(false);
//		    dispose();
		}
	    });
  	buttonPanel.add(cancel);

	java.awt.Dimension paneDim = new java.awt.Dimension(220, 400);
	classListScroll.setPreferredSize(paneDim);
        classListScroll.setMinimumSize(paneDim);
	methodListScroll.setMinimumSize(paneDim);
	methodListScroll.setPreferredSize(paneDim);
	paneDim = new java.awt.Dimension(370, 400);
	poListScroll.setMinimumSize(paneDim);
	poListScroll.setPreferredSize(paneDim);
	methodPanel.add(hide);
	methodPanel.add(methodListScroll);

	JPanel listPanel=new JPanel();
	listPanel.setLayout(new BoxLayout(listPanel, BoxLayout.X_AXIS));
	listPanel.add(classListScroll);
	listPanel.add(methodPanel);
	listPanel.add(poListScroll);

	getContentPane().setLayout(new BoxLayout(getContentPane(), 
						 BoxLayout.Y_AXIS));
	getContentPane().add(listPanel);
	getContentPane().add(buttonPanel);
    }

    /**
     * Sets a new proof obligation list (when the selected method has changed
     * for example) 
     */
    private void setPOList(){
	ProgramMethod m = (ProgramMethod) methodList.getSelectedValue();
	poList.setListData(emptyArray);
	if(m != null && !m.isAbstract() && 
	   !(classType.getJavaType() instanceof InterfaceDeclaration)){
	    SetOfJMLMethodSpec specs = 
		ism.getSpecsForMethod(m);
	    JMLClassSpec cSpec = ism.getSpecForClass(classType);
	    if(specs != null){
		specs = specs.union(ism.getInheritedMethodSpecs(m, classType));
	    }else{
		specs = ism.getInheritedMethodSpecs(m, classType);
	    }
	    IteratorOfJMLMethodSpec mit = specs.iterator();
	    specs = SetAsListOfJMLMethodSpec.EMPTY_SET;
	    boolean pureFound = false;
	    boolean pureInh = false;
	    while(mit.hasNext()){
		JMLMethodSpec s = mit.next();
		if(s instanceof JMLPuritySpec){
		    pureFound = true;
		}
		if(services.getJavaInfo().getKeYJavaType(
		       s.getClassDeclaration()) == classType){
		    specs = specs.add(s);
		}
	    }
	    if(pureInh && !pureFound){
		specs = specs.add(
		    new JMLPuritySpec(m, services, 
				      UsefulTools.buildParamNamespace(m.getMethodDeclaration()), 
				      new LinkedHashMap(), 
				      ism.getSpecForClass(classType), 
				      new NamespaceSet(), javaPath));
	    }
	    if(specs != SetAsListOfJMLMethodSpec.EMPTY_SET || cSpec != null){
		Vector specVector = new Vector();
		if(specs != null){
		    IteratorOfJMLMethodSpec it = specs.iterator();
		    while(it.hasNext()){
			JMLMethodSpec mSpec = it.next();
			specVector.add(mSpec);
			if(mSpec.replaceModelFieldsInAssignable() != null &&
			   !JMLMethodSpec.EVERYTHING.
			   equals(mSpec.getAssignableMode()) &&
			   //                           !mSpec.containsQuantifiedAssignableLocation() &&
			   mSpec.isValid()){
			    specVector.add(new AssignableCheckProofOblInput(
							mSpec, javaPath));
			}
		    }
		}
		if(cSpec != null && (cSpec.containsInvOrConst() || 
				     allInv.isSelected())){
		    specVector.add(cSpec);
		}
		poList.setListData(specVector);
	    }
	}
    }

    /**
     * creates a JMLProofOblInput and starts the proofer.
     */
    private void createProofObl(){
	Object spec = poList.getSelectedValue();
	if(spec instanceof JMLMethodSpec){
	    if(invPost.isSelected()){
		poi = new JMLPostAndInvPO((JMLMethodSpec) spec, javaPath, 
				    allInv.isSelected());
	    }else{
		poi = new JMLPostPO((JMLMethodSpec) spec, javaPath, 
				    allInv.isSelected());
	    }
	}else if(spec instanceof JMLClassSpec){
	    poi = new JMLInvPO((JMLClassSpec) spec,
			       (ProgramMethod) 
			       methodList.getSelectedValue(),
			       javaPath, allInv.isSelected());
	}else if(spec instanceof AssignableCheckProofOblInput){
	    poi = (AssignableCheckProofOblInput) spec;
	    ((AssignableCheckProofOblInput) poi).setAllInvariants(
		allInv.isSelected());
	}	
	if(envMode){
	    ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
	    try {
		pi.startProver(mediator.getProof().env(), poi);
	    } catch(ProofInputException e) {
		//too bad
	    }
	}
    }

    public JMLProofOblInput getPOI(){
	return poi;
    }

    class GUIPackageTreeSelectionListener implements TreeSelectionListener,
                                              java.io.Serializable {
	/**
	 * Sets a new methodlist if the selection in the package tree has
	 * changed and the selected value is a class.
	 */
	public void valueChanged(TreeSelectionEvent e) {
	    Object o = 
		((DefaultMutableTreeNode) e.getPath().getLastPathComponent()).
		getUserObject();
	    if(o instanceof KeYJavaType){
		updateMethodList((KeYJavaType) o); 
	    }
	}
    }

    private void updateMethodList(KeYJavaType kjt){
	if(kjt != null){
	    classType = kjt;
	    ListOfProgramMethod l = inheritedMethods ?
		services.getJavaInfo().getAllProgramMethods(classType) :
		services.getJavaInfo().getKeYProgModelInfo().
		getAllProgramMethodsLocallyDeclared(classType);
	    Vector mVector = new Vector();
	    IteratorOfProgramMethod it = l.iterator();
	    while(it.hasNext()){
		ProgramMethod pm = it.next();
		MethodDeclaration md = pm.getMethodDeclaration();
		if(!md.getName().startsWith("<") ||
		   md.getName().equals(ClassInitializeMethodBuilder.
				       CLASS_INITIALIZE_IDENTIFIER)){
		    addOrdered(mVector, pm);
		}
	    }
	    ListOfProgramMethod ml = services.getJavaInfo().
		getKeYProgModelInfo().getConstructors(classType);
	    IteratorOfProgramMethod mit = ml.iterator();
	    while(mit.hasNext()){
		addOrdered(mVector, mit.next());
	    }
	    methodList.setListData(mVector);
	}
    }
    

    private void addOrdered(Vector v, ProgramMethod m){
	for(int i = 0; i<v.size(); i++){
	    if(m.getName().compareTo(((ProgramMethod) v.get(i)).getName())
	       < 0){
		v.add(i, m);
		return;
	    }
	}
	v.add(m);
    }

    class TextAreaRenderer extends JTextArea implements ListCellRenderer
    {

	private Color getColor(Object o){
	    if(o instanceof JMLNormalMethodSpec){
		return new Color(230, 255, 230);
	    }else if(o instanceof JMLExceptionalMethodSpec){
		return new Color(255, 210, 210);
	    }else if(o instanceof JMLMethodSpec){
		return Color.LIGHT_GRAY;
	    }else if(o instanceof AssignableCheckProofOblInput){
		return new Color(255, 255, 190);
	    }else{
		return new Color(230, 230, 255);
	    }	   
	}

        public TextAreaRenderer()
        {
	    setLineWrap(false);
	    setWrapStyleWord(false);
        }


        public Component getListCellRendererComponent(JList list, Object value,
            int index, boolean isSelected, boolean cellHasFocus)
        {
            setText(value.toString());
	    if((value instanceof JMLSpec) && !((JMLSpec) value).isValid()){
		setBackground(Color.DARK_GRAY);
		setForeground(Color.GRAY);
		setEnabled(false);
	    }else{
		setBackground(isSelected ? Color.BLACK : getColor(value));
		setForeground(isSelected ? Color.WHITE : Color.BLACK);
		setEnabled(true);
	    }
            return this;
        }
    }


}
