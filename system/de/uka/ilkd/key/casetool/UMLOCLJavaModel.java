// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.casetool;

import java.io.File;
import java.io.IOException;
import java.util.Iterator;

import recoder.ServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Field;
import recoder.abstraction.Method;

import recoder.io.DefaultSourceFileRepository;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.declaration.TypeDeclaration;
import recoder.list.*;
import recoder.service.DefaultSourceInfo;
import recoder.util.FileCollector;
import tudresden.ocl.check.types.Type;
import de.uka.ilkd.key.java.Services;

/**
 * @deprecated
 */
public class UMLOCLJavaModel implements UMLOCLModel {
    //debug flag
    private static final boolean DEBUG = false;

    protected SourceFileRepository sfr;
    protected String projectRoot;
    protected HashMapOfClassifier classifiers;
    protected HashMapOfAssociations associations;
    protected JavaOCLTypeMap typeMap = null;
    
    private UMLOCLJavaModel() {
    }
    /**@deprecated */
    public UMLOCLJavaModel(String projectRoot) {
        this.projectRoot  = projectRoot;
        this.projectRoot  = new File(projectRoot).getAbsolutePath();
        this.classifiers  = new HashMapOfClassifier();
        this.associations = new HashMapOfAssociations();        
        initRecoder();        
    }
    
    public UMLOCLJavaModel(Services services, String projectRoot) {
	this.projectRoot  = projectRoot;
	this.projectRoot  = new File(projectRoot).getAbsolutePath();
	this.classifiers  = new HashMapOfClassifier();
	this.associations = new HashMapOfAssociations();
        if(services != null) {
            ServiceConfiguration crsc = 
                services.getJavaInfo().getKeYProgModelInfo().getServConf();
            sfr = crsc.getSourceFileRepository();
        } else {
            initRecoder();
        }
    }

    protected JavaOCLTypeMap getJavaOCLTypeMap
	(HashMapOfClassifier classifier) {
	
	return new JavaOCLTypeMap(classifiers);
    }
    
    public HashMapOfClassifier getUMLOCLClassifiers() {
	   

	final CompilationUnitList cuList = sfr.getCompilationUnits();
	
	// find classes
	findAllClasses(cuList);	

	if (DEBUG) { printClasses(); }

	typeMap = getJavaOCLTypeMap(classifiers);
	
	// find attributes and methods	
	for (int i=0, cuListSize = cuList.size(); i < cuListSize; i++) {
	    final CompilationUnit unit = cuList.getCompilationUnit(i);	    
	    for (int j = 0, typeCount = unit.getTypeDeclarationCount(); 
		 j < typeCount; j++) {

		final TypeDeclaration td = unit.getTypeDeclarationAt(j);	
		findAllAttributes(td);		
		findAllMethods(td);

	    }
	}

	if (DEBUG) { printTypeMembers(); }
	
	return classifiers;
    }

    protected UMLOCLClassifier createUMLOCLClassifier(ClassType ct) {
	return new UMLOCLClassifier(ct.getName(), ct.getFullName());
    }

    private UMLOCLClassifier ensureUMLOCLClassifier(ClassType ct) {
	UMLOCLClassifier cls = classifiers.getClassifier(ct.getName());
	if (cls == null) {			
	    cls = createUMLOCLClassifier(ct);
	    classifiers.putClassifier(ct.getName(),cls);
	} 
	return cls;
    }


    protected void findAllClasses(CompilationUnitList cuList) {	
	for (int i=0, cuListSize = cuList.size(); i < cuListSize; i++) {
	    final CompilationUnit pa = cuList.getCompilationUnit(i);
	    
	    for (int j = 0, tdCount = pa.getTypeDeclarationCount(); j < tdCount; j++) {
		final TypeDeclaration td = pa.getTypeDeclarationAt(j);
		final UMLOCLClassifier cls = ensureUMLOCLClassifier(td);
		// now find all supertypes of this class
		final ClassTypeList supertypes = td.getAllSupertypes();				
		for (int k = 1, supSize = supertypes.size(); k < supSize; k++) {
		    final ClassType st = supertypes.getClassType(k);
		    cls.addSupertype(st.getName(), ensureUMLOCLClassifier(st));
		}
	    }	
	}
    }


    private void findAllMethods(TypeDeclaration td) {
	
	final UMLOCLClassifier cls = 
	    classifiers.getClassifierByFullName(td.getFullName());
	final MethodList ml = td.getAllMethods();
	for (int l = 0, mlSize=ml.size(); l < mlSize; l++) {
	    final Method meth = ml.getMethod(l);
	    recoder.abstraction.Type retType = meth.getReturnType();
	    tudresden.ocl.check.types.Type ret2 = typeMap.getTypeFor(retType, classifiers);

	    if (ret2 == null) {
		ret2 = new UMLOCLClassifier(retType.getName(), retType.getFullName());
		classifiers.putClassifier(retType.getName(), (UMLOCLClassifier) ret2);
	    }


	    final TypeList ctl = meth.getSignature();
	    final Type[] paramsArray = new Type[ctl.size()];
	    final StringBuffer methodSignatureStr = new StringBuffer(meth.getName());
	    methodSignatureStr.append("(");
	    
	    for (int k = 0, ctlSize = ctl.size(); k < ctlSize; k++) {		
		final recoder.abstraction.Type par = ctl.getType(k);
		final String parTypeFullName = par.getFullName();


		methodSignatureStr.append(parTypeFullName);
		if (k < ctlSize - 1) {
		    methodSignatureStr.append(",");
		} 
		
		paramsArray[k] = typeMap.getTypeFor(par, classifiers);
		if (paramsArray[k] == null) {
		    classifiers.putClassifier
			(par.getName(), new UMLOCLClassifier(par.getName(),
							     parTypeFullName));
		    paramsArray[k] = typeMap.getTypeFor(par, classifiers);
		}
	    }
	    methodSignatureStr.append(")");
	    final String name = methodSignatureStr.toString();

	    final UMLOCLBehaviouralFeature behaviouralFeature = (retType == null) ? 
		new UMLOCLBehaviouralFeature(name, paramsArray):
		new UMLOCLBehaviouralFeature(name, ret2, paramsArray);
	    cls.addFeature(name, behaviouralFeature);
	}	
    }
    
	
    private void findAllAttributes(TypeDeclaration td) {
	final FieldList fl = td.getAllFields();
	final UMLOCLClassifier clf = classifiers.getClassifierByFullName(td.getFullName());
	if (clf==null) {		
	    throw new IllegalStateException("Classifier not found: "
					    +td.getFullName());
	}
	for (int l = 0, flSize = fl.size(); l < flSize; l++) {
	    final Field field = fl.getField(l);
	    final recoder.abstraction.Type fieldType = field.getType();

	    Type type = typeMap.getTypeFor(fieldType, classifiers);	    
	    if (type == null) {
		type = new UMLOCLClassifier(fieldType.getName(), 
					    fieldType.getFullName());
		classifiers.putClassifier(fieldType.getName(), 
					  (UMLOCLClassifier) type);
	    }
	    clf.addFeature(field.getName(), 
			   new UMLOCLStructuralFeature(field.getName(), type));
	}		
    }

    // replace recoder2key by pure recoder 
    private void initRecoder() {
	de.uka.ilkd.key.java.Services services = 
	    new de.uka.ilkd.key.java.Services();
	de.uka.ilkd.key.java.Recoder2KeY r2k = 
	    new de.uka.ilkd.key.java.Recoder2KeY
		(services, new de.uka.ilkd.key.logic.NamespaceSet());
	// comment this if OCLDL does not needs to access the java classes	
	r2k.parseSpecialClasses(); 
	ServiceConfiguration crsc = 
	    services.getJavaInfo().getKeYProgModelInfo().getServConf();
	sfr = crsc.getSourceFileRepository();
	new DefaultSourceInfo(crsc);
        StringArrayList files = collectJavaFiles(projectRoot);
        for (int i=0, sz = files.size(); i<sz; i++) {         
            final String path = files.getString(i);
            if (path != null) { 
                try {      
                    sfr.getCompilationUnitFromFile(path); 
                } catch (recoder.ParserException e){
                    System.out.println("Exception occurred while "+
                                       "reading in Java sources: " + e);
                }
            }
        }
    }

    private StringArrayList collectJavaFiles(String dir) {
 	final FileCollector col = new FileCollector(dir);
 	final StringArrayList list = new StringArrayList();
 	while (col.next(DefaultSourceFileRepository.JAVA_FILENAME_FILTER)) {
 	    String path;
 	    try {
 		path = col.getFile().getCanonicalPath();
 	    } catch (IOException ioe) {
 		path = col.getFile().getAbsolutePath();
 	    }
 	    list.add(path);
 	} 	
 	return list;	
    }

    
    // Debugging stuff
        private void printClasses() {
	System.out.println("------------- found the following "+
			   "classes ------------------");
	Iterator it = classifiers.values().iterator();
	UMLOCLClassifier c;
	while (it.hasNext()) {
	    c = (UMLOCLClassifier)it.next();
	    System.out.println(c.getName());
	}
    }

    private void printTypeMembers() {
	System.out.println("------------- found the following "+
			   "methods and attributes ------------------");
	Iterator cit = classifiers.values().iterator();
	UMLOCLClassifier c;
	while (cit.hasNext()) {
	    c = (UMLOCLClassifier)cit.next();
	    HashMapOfFeatures feat = c.features();
	    Iterator it = feat.values().iterator();
	    UMLOCLFeature f;
	    while (it.hasNext()) {
		f = (UMLOCLFeature)it.next();
		if (f instanceof UMLOCLBehaviouralFeature)
		    System.out.println("Method    "+c.getName()+
				       " :: "+f.getName()+"  "+f.getType());
		if (f instanceof UMLOCLStructuralFeature)
		    System.out.println("Attribute "+c.getName()+
				       " :: "+f.getName());
	    } 
	}
    }


}
