// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.casetool.together;

import java.io.File;
import java.util.Enumeration;
import java.util.Iterator;

import com.togethersoft.openapi.ide.project.IdeProject;
import com.togethersoft.openapi.ide.project.IdeProjectManagerAccess;
import com.togethersoft.openapi.rwi.*;
import com.togethersoft.openapi.sci.SciModel;
import com.togethersoft.openapi.sci.SciModelAccess;

import de.uka.ilkd.key.casetool.HashMapOfClassifier;
import de.uka.ilkd.key.casetool.UMLOCLAssociation;
import de.uka.ilkd.key.casetool.UMLOCLClassifier;
import de.uka.ilkd.key.casetool.UMLOCLJavaModel;
import de.uka.ilkd.key.java.Services;

public class UMLOCLTogetherModel extends UMLOCLJavaModel {
    //debug flag
    private static final boolean DEBUG = false;
    private static String pathSep = File.separator;
    private static final String TOGETHER_UNIQUE_NAME_PREFIX = "<oiref:java#Class#";
    private static final String TOGETHER_UNIQUE_NAME_POSTFIX = ":oiref>";

    public UMLOCLTogetherModel() {
        super(getTogetherProjectDir());
    }

    public UMLOCLTogetherModel(Services services) {
	super(services, getTogetherProjectDir());
    }

    public static String getTogetherProjectDir() {
	IdeProject prj = IdeProjectManagerAccess
	    .getProjectManager().getActiveProject();
	if (prj != null) {
	    String tprFile = prj.getFileName();
	    return  tprFile.substring(0, tprFile.lastIndexOf(pathSep));
	} else
	    return "";
    }

    
    public HashMapOfClassifier getUMLOCLClassifiers() {
	      
	super.getUMLOCLClassifiers();
	// find associations
	RwiModel rwiModel = RwiModelAccess.getModel();		
	Enumeration rwiRoots=rwiModel.
	    rootPackages(RwiProperty.MODEL);
	while (rwiRoots.hasMoreElements()) {
	    RwiPackage rwiPackage = (RwiPackage) rwiRoots.nextElement();
	    processAssociations(rwiPackage);
	}

	if (DEBUG)
	    System.out.println("------------- found the following "+
			       "associations ------------------");

	Iterator cit = classifiers.values().iterator();
	UMLOCLClassifier c;
	while (cit.hasNext()) {
	    c = (UMLOCLClassifier)cit.next();
	    Iterator it = c.getAssociations().values().iterator();
	    UMLOCLAssociation assoc;
	    while (it.hasNext()) {
		assoc = (UMLOCLAssociation)it.next();
		if (DEBUG)
		    System.out.println("assoc from: "
				       +assoc.getSource().getName()+
				       " to: "+assoc.getTarget().getName());
	    }
	}
	return classifiers;
    }

    protected void processAssociations(RwiPackage rwiPackage){	
	RwiModel rwiModel = RwiModelAccess.getModel();

	Enumeration rwiNodesEnum = rwiPackage.nodes();
	RwiNode rwiNode;
	TogetherModelClass cls;
	while (rwiNodesEnum.hasMoreElements()){
	    rwiNode = (RwiNode) rwiNodesEnum.nextElement();
	    cls = new TogetherModelClass(rwiNode, rwiModel, null);
	    cls.getAssociations(classifiers);
	}	
	Enumeration subpackages = rwiPackage.subpackages();
	while (subpackages.hasMoreElements()) {
	    RwiPackage subpackage = (RwiPackage) subpackages.nextElement();
	    processAssociations(subpackage);
	}
    }

    /** Given the full name (i.e. including package prefix, e.g. "java.lang.Object") 
     *  of a classifier contained in the current model, this method returns the
     *  corresponding TogetherReprModelClass.
     * @param fullName the name, including package prefix, of a classifier
     * in the current UML model.
     * @return the corresponding TogetherReprModelClass
     */
    public TogetherModelClass getTogetherReprModelClass(String fullName) {
	String uniqueName = TOGETHER_UNIQUE_NAME_PREFIX + fullName 
	    + TOGETHER_UNIQUE_NAME_POSTFIX;
	RwiModel rwiModel = RwiModelAccess.getModel();
	RwiElement elem = rwiModel.findElement(uniqueName);
	TogetherModelClass togetherClass = null;
	if (elem != null && elem instanceof RwiNode) {
	    RwiNode rwiNode = (RwiNode)elem;
	    RwiDiagram diagram = rwiNode.getContainingPackage().getPhysicalDiagram();
	    togetherClass
		= new TogetherModelClass(rwiNode, rwiModel, diagram);
	}
	return togetherClass;
    }
}
