// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together;

import java.io.File;
import java.util.*;

import com.togethersoft.openapi.ide.project.IdeProject;
import com.togethersoft.openapi.ide.project.IdeProjectManager;
import com.togethersoft.openapi.ide.project.IdeProjectManagerAccess;
import com.togethersoft.openapi.rwi.*;
import com.togethersoft.openapi.sci.SciElement;
import com.togethersoft.openapi.sci.SciModel;
import com.togethersoft.openapi.sci.SciModelAccess;

import de.uka.ilkd.key.casetool.*;
import de.uka.ilkd.key.collection.IteratorOfString;
import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.collection.SLListOfString;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.Debug;

/**
 * Central point of access to Together model.
 */
public class TogetherModelClass extends TogetherReprModel 
    implements UMLModelClass{

    private static final String CLASS="Class";

    private RwiNode orig;
    private RwiModel currRwiModel;
    private RwiDiagram currRwiDiagram;

    private RwiNode origParent;
    private boolean origParentAlreadySet = false;
    
    private String name;
    private String inv;
    private String fullName;
    private String throughout;
    private String rootDir;
    
    
    public TogetherModelClass(RwiNode theOrig, 
                              RwiModel model, 
			      RwiDiagram diag) {
	orig = theOrig;
	currRwiModel = model;
	currRwiDiagram = diag;
	name = orig.getProperty(RwiProperty.NAME);
	fullName = orig.getProperty(RwiProperty.FULL_NAME);
	inv =  orig.getProperty("invariants");
	throughout = orig.getProperty("throughout");
	rootDir = createRootDirectory();
    }


    public String getClassName(){
	return name;
    }

    
    public String getContainingPackage() {
	String localFullName = getFullClassName();
	if (localFullName.lastIndexOf(".")==-1) {
	    return null;
	} else {
	    return localFullName.substring
		(0,localFullName.lastIndexOf("."));
	}
    }

    
    public String getFullClassName(){
	return fullName;
    }

    
    // looks if orig has a parent and set it if needed
    private RwiNode getOrigParent(){
	if (origParentAlreadySet){
	    return origParent;
	}else{
	    if (orig.getProperty(RwiProperty.EXTENDS)==null){
		origParent = null;
	    }else{
		Enumeration extended 
		    = orig.properties(RwiProperty.EXTENDS);
		while (extended.hasMoreElements()){
		    RwiProperty nextExtended=(RwiProperty) extended.nextElement();
		    RwiPropertyMap subpropertiesContainer 
			= nextExtended.getSubproperties();
		    RwiElement foundClassOrInterface 
			= currRwiModel.findElement
			(subpropertiesContainer.getProperty
			 (RwiProperty.REFERENCED_ELEMENT));
                    if (foundClassOrInterface != null 
			&& foundClassOrInterface.getProperty
			(RwiProperty.SHAPE_TYPE).equals(RwiShapeType.CLASS)){
			// we have found from the parents the 
			// (unique iff it exists)
			// element which is a class
			RwiReference foundRwiReference 
			    = currRwiDiagram.findReference
			    (foundClassOrInterface);
                        if (foundRwiReference == null){
			    // there is a superclass but not in the 
			    // current diagram
                            origParentAlreadySet = true;
                            return null;
                        }
                        assert foundRwiReference instanceof RwiNodeReference : 
                            "Unexpected type.";
                        RwiNodeReference foundRwiNodeReference 
                            = (RwiNodeReference) foundRwiReference;                        
                        origParent = foundRwiNodeReference.getNode();
		    }
		} //while
	    }
	    origParentAlreadySet = true;
	}
	return origParent;
    }


    // Now, a service for ReprModelMeth
    // @param aUniqueMethName is a name getting from aRwiMember.getUniqueName()
    // @return the method declaration of param in the parents of the current
    //         class
    public RwiMember findParentMeth(String aUniqueMethName){
	String origClassName = getFullClassName();
	String candMethName = substituteCNinUniqueMethName(aUniqueMethName, 
							   origClassName);
	if (candMethName.equals(aUniqueMethName)){
	    // a Method of aUniqueMethName exists within orig
	    // So, we have to ask the parent
	    if (getOrigParent() == null){
		return null;
	    }else{
		TogetherModelClass parentReprClass 
		    = new TogetherModelClass(getOrigParent(), 
						 currRwiModel, 
						 currRwiDiagram);
		return (parentReprClass.findParentMeth(aUniqueMethName));
	    }
	}else{
	    // we have to look if candMethName really exists in the model
	    // If not, we ask our parent
	    RwiMember returnvalue = (RwiMember) currRwiModel.findElement
		(candMethName);
	    if (returnvalue == null){
		if (getOrigParent() != null){
		    TogetherModelClass parentReprClass 
			= new TogetherModelClass(getOrigParent(), 
						     currRwiModel, 
						     currRwiDiagram);
		    returnvalue 
			= parentReprClass.findParentMeth(aUniqueMethName);
		}
	    }
	    return returnvalue;
	}
    }
		

    private String substituteCNinUniqueMethName(String uName, 
						String newClassName){
	// region between 2nd and 3rd '#' is substituted by newClassName
	int firstOcc = uName.indexOf('#', 0);
	int secondOcc = uName.indexOf('#', firstOcc + 1);
	int thirdOcc = uName.indexOf('#', secondOcc +1 );
	String beginning = uName.substring(0, secondOcc + 1);
	String ending = uName.substring(thirdOcc, uName.length() );
	return beginning + newClassName + ending;
    }


    public String getMyInv() {
	return ((inv == null) ? "" : inv);
    }

    
    public String getMyThroughout() {
	return ((throughout == null) ? "" : throughout);
    }
    
    
    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     * @author Kristofer Johannisson
     */
    public void setMyInv(String inv) {
	this.inv = inv;
	orig.setProperty("invariants", inv);
    }
    
        
    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     * @author Kristofer Johannisson
     */
    public void setMyInvGFAbs(String inv) {	
	orig.setProperty("invariantGFAbstractSyntax", inv);
    }
    
    
    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     * @author Kristofer Johannisson
     */
    public String getMyInvGFAbs() {
	String result = orig.getProperty("invariantGFAbstractSyntax");
	if (result == null)
	    return "";
	else
	    return result;
    }
    

    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     * @return the invariant of the parent
     */
    public String getParentInv() { 
	if (getOrigParent() != null){
	    ModelClass parentRepr 
		= new TogetherModelClass(getOrigParent(), 
					     currRwiModel, 
					     currRwiDiagram);
		return parentRepr.getMyInv();
	}
	else{
	    return "";
	}
    }

    
    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     * @return the classname of the parent
     */
    public String getParentClassName() {
		if (getOrigParent() != null){
	    	ModelClass parentRepr 
		    = new TogetherModelClass(getOrigParent(), 
						 currRwiModel, 
						 currRwiDiagram);
			return parentRepr.getClassName();
		}
		else{
	    	return "";
		}
    }
   

    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     */
    public boolean hasOrigParent() {
        return (getOrigParent() != null);
    }

    


    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     * @return a vector of ModelMethod
     */
    public Vector getParentOps() {
	if (getOrigParent() != null){
	    UMLModelClass parentRepr 
		= new TogetherModelClass(getOrigParent(), 
					     currRwiModel, 
					     currRwiDiagram);
		return parentRepr.getOps();
	}
	else{
	    return null;
	}
     }

    
    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     *  @return a vector of String
     */
    public Vector getInheritedOpNames() {
	Vector opNames = getInheritedOps();
	Vector result = new Vector();
	if (opNames != null){
	    for (int i=0; i < opNames.size(); i++) 
		result.addElement(((TogetherModelMethod)
				   opNames.elementAt(i)).getName());
	    return result;
	}
	else{
	    return null;
	}

     }

    
    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     *  @return a vector of ReprModelMethod
     */
    public Vector getInheritedOps() {
	Vector opVector = getParentOps();
	Vector result = new Vector();
	TogetherModelMethod op;
	if (opVector != null){
	    for (int i=0; i < opVector.size(); i++) {
		op = (TogetherModelMethod)(opVector.elementAt(i));
		if (!op.isConstructor() &&  !op.isPrivate()) {
		    result.addElement(opVector.elementAt(i));
		}
		
	    }
	    return result;
	}
	else{
	    return null;
	}

     }

    
    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     * @return a vector of String
     */
     public Vector getOpNames() {
        Enumeration allMembers = orig.members();
        Vector opMemberNames = new Vector();
        while (allMembers.hasMoreElements()){
            RwiMember nextMember = (RwiMember) allMembers.nextElement();
            if(RwiShapeType.OPERATION.equals(nextMember.getProperty
					     (RwiProperty.SHAPE_TYPE))){
                 opMemberNames.add(nextMember.getProperty(RwiProperty.NAME));
            }
        }
        return opMemberNames;
     }


    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     * @return a vector of ReprModelMethod
     */
     public Vector getOps() {
        Enumeration allMembers = orig.members();
        Vector opVector = new Vector();
        while (allMembers.hasMoreElements()){
            RwiMember nextMember = (RwiMember) allMembers.nextElement();
            if(RwiShapeType.OPERATION.equals(nextMember.getProperty
					     (RwiProperty.SHAPE_TYPE))){
		opVector.add(new TogetherModelMethod(nextMember, 
							 currRwiModel, 
							 currRwiDiagram));
            }
        }
        return opVector;
     }
     

    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     */
    private String getAssociationRole(RwiElement rwiMember, 
				      RwiLink link, String which) {
	SciModel model = SciModelAccess.getModel();
	String role;
	role = model.findElement
	    (rwiMember.getUniqueName()).getTagList().
	    getTagValue(which);
	if (role==null){
	    if ("clientRole".equals(which))
		role=link.getSource().toString();
	    else if ("supplierRole".equals(which))
		role=link.getDestination().toString();
	    else 
		return null;
	    role=role.substring(0,1).toLowerCase()+
		role.substring(1,role.length());
	}
	return role;
    }

    
    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     */
    public String getText() {
	return orig.getProperty(RwiProperty.TEXT);
    }
    

    /** relies on a valid backing RWI / SCI model element, i.e. the together
     * project is still valid (opened)
     */
    private HashSet getAllJavaFiles(RwiPackage pac, HashSet v) {	
	Enumeration subpackages=pac.subpackages();
	while (subpackages.hasMoreElements()) {
	    v=getAllJavaFiles((RwiPackage) subpackages.nextElement(), v);
	}
	Enumeration en=pac.nodes();
	while (en.hasMoreElements()) {
	    RwiElement rwin=(RwiElement) en.nextElement();
	    if (rwin.getProperty(RwiProperty.SHAPE_TYPE).equals(CLASS)){
		String filename=rwin.getProperty(RwiProperty.FILE);
		if (filename!=null && filename.endsWith(".java")) {
		    v.add(filename);
		    Debug.out("Let recoder read file: "+filename);
		}	    
	    }
	}
	return v;
    }

    
    /** relies on a valid backing RWI / SCI model element, i.e. the together
     * project is still valid (opened)
     */
    public String[] getClassesInPackage() {	
	HashSet v = new LinkedHashSet();	
	RwiPackage rootPac=orig.getContainingPackage();	
	while (rootPac.getContainingPackage()!=null) {
	    rootPac=rootPac.getContainingPackage();
	}
	v=getAllJavaFiles(rootPac, v);
	String[] strings = new String[v.size()];
	Iterator it = v.iterator();
	int i = 0;
	while (it.hasNext()) {
	    strings[i]=(String)it.next();
	     i++;
	}
	return strings;
    }

    
    /** returns the root directory of the active project */
    public String getRootDirectory() {
	return rootDir;
    }

    
    public String createRootDirectory() {
	IdeProjectManager pm=IdeProjectManagerAccess.getProjectManager();
	IdeProject prj=pm.getActiveProject();
	File f = new File(prj.getFileName());
	return f.getParentFile().getAbsolutePath();
    }

    
    /** returns all classes of the currently loaded project
     */
    public Set getAllClasses() {
	// Put everything in "result" by recursing, set result to an
	// empty HashSet in case this method gets called more than once.
	RwiPackage rootPackage=orig.getContainingPackage();
	//this did not work (Tg bug!?):
	//rootPackage.getContainingPackage()!=null
	while (rootPackage.getContainingPackage()!=null 
	       && rootPackage.getContainingPackage().nodes().hasMoreElements()){
	    rootPackage=rootPackage.getContainingPackage();
	}
	Set result = new LinkedHashSet();
	rwiRecurse(rootPackage.nodes(), result);
	return result;
    }
    
    
     // this method adds to "result"!
    private void rwiRecurse(Enumeration nodeEnum, Set result) {
	RwiNode node = null;
	ModelClass reprClass = null;
	while (nodeEnum.hasMoreElements()) {
	    node = (RwiNode) nodeEnum.nextElement();
	    if (RwiShapeType.CLASS.equals
		(node.getProperty(RwiProperty.SHAPE_TYPE))) {
		// current RwiNode is "node" 
		RwiModel model = RwiModelAccess.getModel();
		RwiDiagram diagram = model.findDiagramFor(node);
		
		reprClass = new TogetherModelClass(node, model, diagram);
		result.add(reprClass);
	    }
	    else {
		rwiRecurse(node.subnodes(), result);
	    }
	}
    }
    
        
    
    public String toString() {
        return getClassName();
    }
    
    
    /**
     * relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     */
    public ListOfModelClass getMyParents() {
        ListOfString parentNames = SLListOfString.EMPTY_LIST;
        RwiModel model = RwiModelAccess.getModel();
        
        Enumeration extended 
                = orig.properties(RwiProperty.EXTENDS);
        while (extended.hasMoreElements()) {
            RwiProperty parentProperty = (RwiProperty) extended.nextElement();
            RwiPropertyMap subProperties = parentProperty.getSubproperties();
            RwiElement parentElement = model.findElement(
                    subProperties.getProperty(RwiProperty.REFERENCED_ELEMENT));
            String parentName = parentElement.getProperty(RwiProperty.FULL_NAME);
            parentNames = parentNames.prepend(parentName);
        }
        
        Enumeration implemented 
                = orig.properties(RwiProperty.IMPLEMENTS);
        while (implemented.hasMoreElements()) {
            RwiProperty parentProperty = (RwiProperty) implemented.nextElement();
            RwiPropertyMap subProperties = parentProperty.getSubproperties();
            RwiElement parentElement = model.findElement(
                    subProperties.getProperty(RwiProperty.REFERENCED_ELEMENT));
            String parentName = parentElement.getProperty(RwiProperty.FULL_NAME);
            parentNames = parentNames.prepend(parentName);
        }
        
        ListOfModelClass result = SLListOfModelClass.EMPTY_LIST;
        
        Iterator it = getAllClasses().iterator();
        while(it.hasNext()) {
            UMLModelClass modelClass = (UMLModelClass)(it.next());
            IteratorOfString it2 = parentNames.iterator();
            while(it2.hasNext()) {
                if(it2.next().equals(modelClass.getFullClassName())) {
                    result = result.prepend(modelClass);
                    break;
                }
            }
        }
        
        return result;
    }
    
    
    /**
     * Helper for getAllAssociations().
     */
    private static RwiMember getMemberForLink(TogetherModelClass modelClass, 
                                              RwiLink link) {
        Enumeration rwiMemberEnum = modelClass.orig.members();
        while(rwiMemberEnum.hasMoreElements()) {
            RwiMember rwiMember = (RwiMember) rwiMemberEnum.nextElement();
            if(rwiMember.getUniqueName().indexOf(link.toString()) != -1) {
                return rwiMember;
            }
        }
        
        return null;
    }
    
    
    /**
     * Helper for createUMLInfo().
     */
    private ListOfAssociation getAllAssociations(Services services) {
        ListOfAssociation result = SLListOfAssociation.EMPTY_LIST;
        
        //get all classes
        Set allClasses = getAllClasses();
        
        //build hash map for looking up classes by their name
        Map /*String -> ModelClass*/ classesByName = new HashMap();
        Iterator it = allClasses.iterator();
        while(it.hasNext()) {
            TogetherModelClass modelClass = (TogetherModelClass) it.next();
            classesByName.put(modelClass.orig.toString(), modelClass);
        }
        
        //iterate over all classes
        SciModel model = SciModelAccess.getModel();
        it = allClasses.iterator();
        while(it.hasNext()) {
            TogetherModelClass sourceClass = (TogetherModelClass) it.next();
            
            //iterate over all links of this class
            Enumeration linkEnum = sourceClass.orig.outgoingLinks();
            while(linkEnum.hasMoreElements()){
                RwiLink link = (RwiLink) linkEnum.nextElement();
                
                //ignore links which are no associations
                if(!link.getProperty(RwiProperty.SHAPE_TYPE)
                        .equals(RwiShapeType.ASSOCIATION)) {
                    continue;
                }
                
                //get target class
                TogetherModelClass targetClass 
                    = (TogetherModelClass) 
                        classesByName.get(link.getDestination().toString());
                if(targetClass == null) {
                    continue;
                }
                                
                //get associated rwiMember in source class
                RwiMember rwiMember = getMemberForLink(sourceClass, link);
                if(rwiMember == null) {
                    continue;
                }
                
                //get multiplicities
                String sourceMultString 
                    = model.findElement(rwiMember.getUniqueName())
                           .getTagList()
                           .getTagValue("clientCardinality");
                Multiplicity sourceMult = Multiplicity.STANDARD;
                if(sourceMultString != null) {             
                    sourceMult = Multiplicity.getMultiplicityFromString(
                                                            sourceMultString);
                }
                String targetMultString 
                    = model.findElement(rwiMember.getUniqueName())
                           .getTagList()
                           .getTagValue("supplierCardinality");
                Multiplicity targetMult = Multiplicity.STANDARD;
                if(targetMultString != null) {
                    targetMult = Multiplicity.getMultiplicityFromString(
                                                            targetMultString);
                }
               
                //get names
                String assocName = model.findElement(rwiMember.getUniqueName())
                                        .getTagList()
                                        .getTagValue("label");
                String sourceRoleName = getAssociationRole(rwiMember, 
                                                           link, 
                                                           "clientRole");
                String targetRoleName = getAssociationRole(rwiMember, 
                                                           link, 
                                                           "supplierRole");
                
                //create association
                AssociationEnd sourceEnd = new AssociationEnd(sourceRoleName,
                                                              sourceMult, 
                                                              sourceClass);
                AssociationEnd targetEnd = new AssociationEnd(targetRoleName,
                                                              targetMult,
                                                              targetClass);
                Association assoc = new Association(services,
                                                    assocName,
                                                    sourceEnd, 
                                                    targetEnd);
                result = result.prepend(assoc);
            }
        }
        
        return result;
    }
    
    
    /**
     * relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     */
    public UMLInfo createUMLInfo(Services services) {
        return new UMLInfo(services, getAllAssociations(services));
    }
    
    
    
    //-------------------------------------------------------------------------
    //deprecated
    //-------------------------------------------------------------------------

    /** relies on a valid backing RWI / SCI model element, i.e. the together
     * project is still valid (opened)
     * @deprecated
     */
    public void getAssociations(HashMapOfClassifier 
                                classifiers) {
        
        SciModel model = SciModelAccess.getModel();
        Enumeration linkEnum = orig.outgoingLinks();
        RwiLink link;
        Multiplicity sourceMult = null, targetMult = null;
        String sourceRole = null, targetRole = null;
        Enumeration rwiMemberEnum;
        RwiMember rwiMember;
        while (linkEnum.hasMoreElements()){
            link = (RwiLink) linkEnum.nextElement();
            //filter out associations
            if (link.getProperty(RwiProperty.SHAPE_TYPE).
                equals(RwiShapeType.ASSOCIATION)){
                // get cardinality and client role
                targetMult = null;
                targetRole = null;
                rwiMemberEnum = orig.members();
                rwiMember = null;
                while (rwiMemberEnum.hasMoreElements()){
                    rwiMember = (RwiMember) rwiMemberEnum.nextElement();
                    if (rwiMember.getUniqueName().indexOf(link.toString())!=-1){
                        SciElement e = model.findElement(rwiMember.getUniqueName());
                        String card = model.findElement
                            (rwiMember.getUniqueName()).getTagList().
                            getTagValue("supplierCardinality");
                        targetMult=Multiplicity.STANDARD;
                        if (card!=null)
                            targetMult= Multiplicity.
                                getMultiplicityFromString(card);
                        
                        targetRole = getAssociationRole
                            (rwiMember, link, "supplierRole");
                        
                        break;
                    }               
                }

                // associations are bi-directional. So we have to add the 
                // association also to the target classifier 

                sourceMult=null;
                sourceRole=null;
                
                String card = model.findElement
                    (rwiMember.getUniqueName()).getTagList().
                    getTagValue("clientCardinality");
                sourceMult=Multiplicity.STANDARD;
                if (card!=null)             
                    sourceMult = Multiplicity.
                        getMultiplicityFromString(card);
                
                sourceRole = getAssociationRole(rwiMember, link, "clientRole");

                UMLOCLClassifier sourceClassifier = 
                    classifiers.getClassifier(orig.toString());
                UMLOCLClassifier targetClassifier = 
                    classifiers.getClassifier(link.getDestination().toString());
                if (sourceClassifier != null && targetClassifier != null) {
                    sourceClassifier.addAssociation
                        (targetRole, new UMLOCLTogetherAssociation
                        (sourceClassifier, sourceRole, sourceMult, 
                         targetClassifier, targetRole, targetMult));
                    targetClassifier.addAssociation
                        (sourceRole, new UMLOCLTogetherAssociation
                        (targetClassifier, targetRole, targetMult,
                         sourceClassifier, sourceRole, sourceMult));

                }
            }
        }
    }    
}
