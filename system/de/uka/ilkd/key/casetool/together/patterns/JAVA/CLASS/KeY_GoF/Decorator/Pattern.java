// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together.patterns.JAVA.CLASS.KeY_GoF.Decorator;

import java.util.Enumeration;
import java.util.Vector;

import com.togethersoft.modules.patterns.UNIVERSAL.PatternBaseException;
import com.togethersoft.modules.patterns.UNIVERSAL.PatternUIBuilder;
import com.togethersoft.openapi.sci.*;
import com.togethersoft.openapi.sci.pattern.SciPatternUtil;
import com.togethersoft.openapi.util.propertyMap.Property;
import com.togethersoft.openapi.util.propertyMap.PropertyMapEvent;
import com.togethersoft.openapi.util.propertyMap.PropertyMapListener;

import de.uka.ilkd.key.casetool.together.keydebugclassloader.KeyPattern;
import de.uka.ilkd.key.casetool.together.patterns.HelperClasses.MyPatternBase.MyCondition;

public class Pattern extends KeyPattern {

    private static final String PATTERN_NAME = "Decorator";
    private MyCondition cond1, cond2;
    private String pageName1;
    private Vector queryVector, copySpecVector;

    public Pattern() {
        setPatternDisplayName(PATTERN_NAME);
    }

    protected void finalize1() throws Throwable {
        //super.finalize();
	superFinalizeSimu();
        if (myUIBuilder != null) {
            myUIBuilder.removeAllListenedInspectorProperties();
            myUIBuilder = null;
        }
        myClassRoleVector.removeAllElements();
        myClassRoleVector = null;
    }

    public boolean prepare1()
    {
        try {
            //super.prepare();
	    superPrepareSimu();
            implementedForJavaOnly();

            setPropertyValue(SELECTED_CLASS_ROLE, null);
            setPropertyValue(LOCAL_COMPONENT, LOCAL_COMPONENT);
            setPropertyValue(CONCRETE_COMPONENT, null);
            setPropertyValue(DECORATOR, DECORATOR);
            setPropertyValue(CONCRETE_DECORATOR, null);
            setPropertyValue(ATTRIBUTE, LOCAL_COMPONENT.toLowerCase());
            setPropertyValue(INITIALIZATION_VARIANT, KEY_CONSTRUCTOR_PARAMETER);
            setPropertyValue(EXPORT_DOCUMENTATION, Boolean.FALSE);
            setPropertyValue(CREATE_PATTERN_LINKS, Boolean.TRUE);

            myClassRoleVector.removeAllElements();

            if (getSelectedClass() == null) {
                addPropertyValue(CONCRETE_COMPONENT, "ConcreteComponent");
                addPropertyValue(CONCRETE_DECORATOR, "ConcreteDecorator");
            }
            else {
                myClassRoleVector.addElement(LOCAL_COMPONENT);
                myClassRoleVector.addElement(CONCRETE_COMPONENT);
                myClassRoleVector.addElement(DECORATOR);

                if (!getSelectedClass().hasProperty(SciProperty.INTERFACE)) {
                    myClassRoleVector.addElement(CONCRETE_DECORATOR);
                }

                String currentRole = null;
                if (findComponentByDecorator(getSelectedClass()) != null) {
                    currentRole = DECORATOR;
                }
                else if (SciPatternUtil.findExtendedPatternLinkClient(getSelectedClass(), PATTERN_NAME, CONCRETE_COMPONENT) != null) {
                    currentRole = CONCRETE_COMPONENT;
                }
                else if (SciPatternUtil.findExtendedPatternLinkClient(getSelectedClass(), PATTERN_NAME, CONCRETE_DECORATOR) != null) {
                    currentRole = CONCRETE_DECORATOR;
                }
                else {
                    currentRole = LOCAL_COMPONENT;
                }
                setPropertyValue(SELECTED_CLASS_ROLE, currentRole);
            }

            initializeInspector();
            assignActivityResponse();

	    //----------------------------------------------------------------

	    //initPattern();
 	    //----------------------------------------------------------------

            return true;
        }
        catch(PatternBaseException e) {
            return false;
        }
    }

    public boolean canApply1()
    {
        try {
            String componentName = classNameShouldBeCorrect(LOCAL_COMPONENT);
            SciClass componentClass = findClassByName(componentName);

            String decoratorName = classNameShouldBeCorrect(DECORATOR);
            SciClass decoratorClass = findClassByName(decoratorName);
            shouldBeWritable(DECORATOR, decoratorClass);

            String attributeName = identifierShouldBeCorrect(ATTRIBUTE);
            if (componentClass != null) {
                checkAttributeName(attributeName, decoratorClass, componentClass);
            }
            else {
                checkAttributeName(attributeName, decoratorClass, componentName);
            }
            checkConcreteElements(componentClass, CONCRETE_COMPONENT, true);

            Enumeration enumeration = propertiesEnumeration(CONCRETE_DECORATOR);
            while (enumeration.hasMoreElements()) {
                String concreteDecoratorName = classNameShouldBeCorrect((Property)enumeration.nextElement());
                if (concreteDecoratorName == null || concreteDecoratorName.length() == 0) {
                    continue;
                }

                SciClass concreteDecoratorClass = findClassByName(concreteDecoratorName);
                cannotBeAnInterface(CONCRETE_DECORATOR, concreteDecoratorClass);
                shouldBeWritable(CONCRETE_DECORATOR, concreteDecoratorClass);
                if (decoratorClass != null) {
                    shouldExtend(concreteDecoratorClass, decoratorClass);
                }
                else {
                    shouldExtend(concreteDecoratorClass, decoratorName);
                }
            }

            if (componentClass != null) {
                shouldExtend(decoratorClass, componentClass);
            }
            else {
                shouldExtend(decoratorClass, componentName);
            }

            return true;
        }
        catch(PatternBaseException e) {
            return false;
        }
    }

    public void apply1() {
        if (!canApply()) {
            return;
        }
        //super.apply();
	superApplySimu();

        String attributeName = getStringPropertyValue(ATTRIBUTE);

/* Get or create Component class. */

        String componentName = getStringPropertyValue(LOCAL_COMPONENT);
        SciClass componentClass = getClassByName(componentName, true);

/* Get or create Decorator class. Create inheritance from Component,
   if this inheritance doesn't exist. Create attribute for Component. */

        String decoratorName = getStringPropertyValue(DECORATOR);
        SciClass decoratorClass = getClassByName(decoratorName, false);
        SciPatternUtil.createInheritance(decoratorClass, componentClass);
        SciAttribute attribute = SciPatternUtil.createAttribute(decoratorClass, componentClass, attributeName, true);
	attribute.setProperty(SciProperty.PRIVATE, false);
	attribute.setProperty(SciProperty.PROTECTED, true);


/* Create sample operation, if all classes are new. */

        if (myAllClassesAreNew) {
            SciOperation sampleOperation = getFactory().newOperation();
            sampleOperation.setName("sampleOperation");
            componentClass.paste(sampleOperation, null, false);
        }

/* Create operations in Decorator class. */

        Enumeration componentOperations = SciUtil.allMembers(componentClass, true);
        while (componentOperations.hasMoreElements()) {
            Object element = componentOperations.nextElement();
            if (!(element instanceof SciOperation)) {
                continue;
            }
            SciOperation componentOperation = (SciOperation)element;
            if (componentOperation.hasProperty(SciProperty.CONSTRUCTOR)) {
                continue;
            }
            if (componentOperation.hasProperty(SciProperty.PRIVATE)) {
                continue;
            }
            SciOperation decoratorOperation = (SciOperation)SciUtil.findMemberBySignature(decoratorClass, componentOperation);
            if (decoratorOperation != null) {
                continue;
            }
            decoratorOperation = (SciOperation)decoratorClass.paste(componentOperation, null, false);
            if (!exportDocumentation()) {
                Enumeration tags = decoratorOperation.getTagList().tags();
                while (tags.hasMoreElements()) {
                    ((SciTag)tags.nextElement()).setValue(null);
                }
            }
            decoratorOperation.setProperty(SciProperty.ABSTRACT, false);
            SciPatternUtil.makeDelegatedImplementation(decoratorOperation, getStringPropertyValue(ATTRIBUTE), false);
        }

/* Add initialization in Decorator class. */

        String initializationVariant = getStringPropertyValue(INITIALIZATION_VARIANT);
        if (KEY_CONSTRUCTOR_PARAMETER.equals(initializationVariant)) {
            SciPatternUtil.createStubConstructors(decoratorClass, componentClass);
            SciPatternUtil.addAttributeToConstructors(attribute);	    
        }
        else if (KEY_SET_METHOD.equals(initializationVariant)) {
            SciPatternUtil.createSetMethod(attribute);
        }

/* Create concrete components. */

        Enumeration enumeration = propertiesEnumeration(CONCRETE_COMPONENT);
        while (enumeration.hasMoreElements()) {
            String concreteComponentName = (String)((Property)enumeration.nextElement()).getValue();
            if (concreteComponentName == null || concreteComponentName.length() == 0) {
                continue;
            }
            SciClass concreteComponentClass = getClassByName(concreteComponentName, false);
            SciPatternUtil.makeStubImplementation(concreteComponentClass, componentClass, false, exportDocumentation());
            if (createPatternLinks()) {
                SciPatternUtil.addPatternLink(componentClass, concreteComponentClass, PATTERN_NAME, null, CONCRETE_COMPONENT, false);
            }
        }

/* Create concrete decorators. */

        enumeration = propertiesEnumeration(CONCRETE_DECORATOR);
        while (enumeration.hasMoreElements()) {
            String concreteDecoratorName = (String)((Property)enumeration.nextElement()).getValue();
            SciClass concreteDecoratorClass = getClassByName(concreteDecoratorName, false);
            SciPatternUtil.makeStubImplementation(concreteDecoratorClass, decoratorClass, true, exportDocumentation());
	    if (KEY_CONSTRUCTOR_PARAMETER.equals(initializationVariant)) {
		SciGenericFactory fac
		    = SciModelAccess.getModel().getGenericFactory(SciLanguage.JAVA);
		try {
		    SciMember constr
			=fac.newMember("public "+concreteDecoratorName+"("
				       +componentName+" c){\n "
				       +"  super(c);\n}", concreteDecoratorClass);
		    concreteDecoratorClass.paste(constr, null, false);
		} catch (com.togethersoft.openapi.sci.SciGenericFactoryException e) {
		    throw new RuntimeException ("Error while expanding pattern");
		}		
	    }
            if (createPatternLinks()) {
                SciPatternUtil.addPatternLink(decoratorClass, 
					      concreteDecoratorClass, 
					      PATTERN_NAME, null, 
					      CONCRETE_DECORATOR, false);

	    
            }
        }

/* Create pattern link. */

        if (createPatternLinks()) {
            SciPatternUtil.addPatternLink(componentClass, decoratorClass, PATTERN_NAME, null, DECORATOR, false);
        }

        myClassRoleVector.removeAllElements();
        myUIBuilder.removeAllListenedInspectorProperties();
        myUIBuilder = null;

	//----------------------------------------------------------------
	//        applyOCLSchemes();
	//----------------------------------------------------------------


	if (isBooleanFieldSelected("Copy spec from methods") 
	    && componentClass!=null){

	    enumeration = propertiesEnumeration(CONCRETE_COMPONENT);
	    while (enumeration.hasMoreElements()) {
		String concreteComponentName = (String)
		    ((Property)enumeration.nextElement()).getValue();
		if (concreteComponentName == null || 
		    concreteComponentName.length() == 0) {
		    continue;
		}
		SciClass concreteComponentClass = 
		    getClassByName(concreteComponentName, false);
		for (int i=0; i<copySpecVector.size(); i++){
		    if (isBooleanFieldSelected(copySpecVector.elementAt(i).toString())){
			String method=copySpecVector.elementAt(i).
			    toString().substring(indent.length());
			copySpecFromTo(componentClass, method, concreteComponentClass);
		    } 
		}	

	    }
	    enumeration = propertiesEnumeration(CONCRETE_DECORATOR);
	    while (enumeration.hasMoreElements()) {
		String concreteDecoratorName = (String)
		    ((Property)enumeration.nextElement()).getValue();		
		if (concreteDecoratorName == null || 
		    concreteDecoratorName.length() == 0) {
		    continue;
		}
		SciClass concreteDecoratorClass = 
		    getClassByName(concreteDecoratorName, false);
		for (int i=0; i<copySpecVector.size(); i++){
		    if (isBooleanFieldSelected(copySpecVector.elementAt(i).toString())){
			String method=copySpecVector.elementAt(i).
			    toString().substring(indent.length());
			copySpecFromTo(componentClass, method, concreteDecoratorClass);
		    } 
		}		
	    }
	}


	if (isBooleanFieldSelected("SimplyDecorated")){
	    String dec=getStringPropertyValue(DECORATOR);
	    SciMember newAttribute=null;
	    try{		    
		newAttribute = (SciMember)SciModelAccess.getModel().
		    getGenericFactory(SciLanguage.JAVA).
		    newMember("private "+dec+" lnk"+dec+";", 
				 decoratorClass);
		newAttribute.getTagList().setTagValue("clientCardinality","0..*");
		newAttribute.getTagList().setTagValue("clientRole",
						      "allInnerDecorators");
	    }
	    catch( SciGenericFactoryException e ) {		    
		System.out.println("Error creating specification\n");
	    }		
	    decoratorClass.paste(newAttribute, null, false);
	    String newInv = "if (not (self."+
		getStringPropertyValue(ATTRIBUTE)+".oclIsKindOf("+
		dec+")))\n then (allInnerDecorators->isEmpty) \n"+
		"else (allInnerDecorators=self."+
		getStringPropertyValue(ATTRIBUTE)+".oclAsType("+
		dec+").allInnerDecorators->\nincluding(self."+
		getStringPropertyValue(ATTRIBUTE)+".oclAsType("+
		dec+"))) endif";
	    String oldInv=decoratorClass.getTagList().getTagValue("invariants");
	    if (oldInv==null) {
		decoratorClass.getTagList().setTagValue("invariants",newInv);
	    } else {
		decoratorClass.getTagList().setTagValue("invariants",oldInv+" \nand "+newInv);
	    }
	    enumeration = propertiesEnumeration(CONCRETE_DECORATOR);
	    while (enumeration.hasMoreElements()) {
		String concreteDecoratorName = (String)
		    ((Property)enumeration.nextElement()).getValue();
		if (concreteDecoratorName == null || 
		    concreteDecoratorName.length() == 0) {
		    continue;
		}
		SciClass concreteDecoratorClass = 
		    getClassByName(concreteDecoratorName, false);
		newInv = "self.allInnerDecorators->"+
		    "forAll(cd | not(cd.oclIsKindOf("+
		    concreteDecoratorName+")))";
		oldInv=concreteDecoratorClass.getTagList().getTagValue("invariants");
		if (oldInv==null) {
		    concreteDecoratorClass.getTagList().setTagValue("invariants",newInv);
		} else {
		    concreteDecoratorClass.getTagList().setTagValue("invariants",oldInv+" \nand "+newInv);
		}
		String decInv=decoratorClass.getTagList().getTagValue("invariants");
		oldInv=concreteDecoratorClass.getTagList().getTagValue("invariants");
		if (oldInv==null) {
		    concreteDecoratorClass.getTagList().setTagValue("invariants",decInv);
		} else {
		    concreteDecoratorClass.getTagList().setTagValue("invariants",decInv+" \nand "+oldInv);
		}
		
	    }
   	}

	if (isBooleanFieldSelected("Specify Queries")){

	    Enumeration opEnum = decoratorClass.operations();
	    SciOperation op;
	    while (opEnum.hasMoreElements()){
		op = (SciOperation)opEnum.nextElement();
		for (int i=0; i<queryVector.size(); i++){
		    if (isBooleanFieldSelected(queryVector.elementAt(i).toString()) &&
			queryVector.elementAt(i).toString().equals(indent+op.getName()+" ")){
			op.getTagList().setTagValue("postconditions","result=self."+
						    getStringPropertyValue(ATTRIBUTE)+
						    "."+op.getName()+"()");
		    } 
		}
	    }
	}
    }

    private SciClass findComponentByDecorator(SciClass decorator) {
        if (decorator == null) {
            return null;
        }

        Enumeration inheritances = decorator.getExtendsList().inheritances();
        while (inheritances.hasMoreElements()) {
            SciClass component = (SciClass)
            ((SciInheritance)inheritances.nextElement()).getReferencedElement();
            if (component != null) {
                Enumeration attributes = decorator.attributes();
                while (attributes.hasMoreElements()) {
                    if (component.equals(((SciAttribute)attributes.nextElement()).getType().getReferencedElement())) {
                        return component;
                    }
                }
            }
        }

        if (getLanguage().equals(SciLanguage.JAVA) && !decorator.hasProperty(SciProperty.INTERFACE)) {
            inheritances = decorator.getImplementsList().inheritances();
            while (inheritances.hasMoreElements()) {
                SciClass component = (SciClass)
                    ((SciInheritance)inheritances.nextElement()).getReferencedElement();
                if (component != null) {
                    Enumeration attributes = decorator.attributes();
                    while (attributes.hasMoreElements()) {
                        if (component.equals(((SciAttribute)attributes.nextElement()).getType().getReferencedElement())) {
                            return component;
                        }
                    }
                }
            }
        }

        return null;
    }

    protected void initializeInspector() {
        try {
            myUIBuilder = null;
            myUIBuilder = createUIBuilder(true);
	    
            Vector inspectorPropertiesVector = new Vector();
	    
            // Create page
            pageName1 = "Pattern properties";
            if (myUIBuilder.addInspectorPage(pageName1, PatternUIBuilder.UIPresentation.Table) == null) {
                throw new PatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }

	    //----------------------------------------------------------------
	    setUIBuilder(myUIBuilder);
	    setPageName(pageName1);
	    //----------------------------------------------------------------

            if (getStringPropertyValue(SELECTED_CLASS_ROLE) != null) {
                if (myUIBuilder.addPropertyToPage(pageName1, SELECTED_CLASS_ROLE, SELECTED_CLASS_ROLE,
                    PatternUIBuilder.PropertyType.StringChooser, myClassRoleVector.toArray()) == null) {
                    throw new PatternBaseException(CANNOT_CREATE_PATTERN_UI);
                }
                inspectorPropertiesVector.addElement(SELECTED_CLASS_ROLE);
            }

            boolean allowInterface = true;
            if (myUIBuilder.addClassPropertyToPage(pageName1, LOCAL_COMPONENT, LOCAL_COMPONENT,
                PatternUIBuilder.PropertyType.SingleValue, allowInterface) == null) {
                throw new PatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(LOCAL_COMPONENT);

            allowInterface = true;
            if (myUIBuilder.addClassPropertyToPage(pageName1, CONCRETE_COMPONENT, CONCRETE_COMPONENT,
                PatternUIBuilder.PropertyType.MultiValue, allowInterface) == null) {
                throw new PatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(CONCRETE_COMPONENT);

            allowInterface = false;
            if (myUIBuilder.addClassPropertyToPage(pageName1, DECORATOR, DECORATOR,
                PatternUIBuilder.PropertyType.SingleValue, allowInterface) == null) {
                throw new PatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(DECORATOR);

            allowInterface = false;
            if (myUIBuilder.addClassPropertyToPage(pageName1, CONCRETE_DECORATOR, CONCRETE_DECORATOR,
                PatternUIBuilder.PropertyType.MultiValue, allowInterface) == null) {
                throw new PatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(CONCRETE_DECORATOR);

            if (myUIBuilder.addPropertyToPage(pageName1, ATTRIBUTE, ATTRIBUTE,
                PatternUIBuilder.PropertyType.String) == null) {
                throw new PatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(ATTRIBUTE);

            // Add INITIALIZATION_VARIANT property
            String[] items = new String[] { KEY_NONE, KEY_CONSTRUCTOR_PARAMETER, KEY_SET_METHOD };
            if (myUIBuilder.addPropertyToPage(pageName1, INITIALIZATION_VARIANT, INITIALIZATION_VARIANT,
                PatternUIBuilder.PropertyType.StringChooser, items) == null) {
                throw new PatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(INITIALIZATION_VARIANT);

            if (myUIBuilder.AddExportDocumentationProperty(pageName1) == null) {
                throw new PatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(EXPORT_DOCUMENTATION);

            if (myUIBuilder.AddCreatePatternLinksProperty(pageName1) == null) {
                throw new PatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(CREATE_PATTERN_LINKS);

 	    addBooleanFieldItem("Copy spec from methods",false);
            inspectorPropertiesVector.addElement("CopySpec");
	    cond1=new MyCondition();

	    copySpecVector=new Vector();
	    SciClass componentClass = getSelectedClass();
	    if (componentClass!=null){
		Enumeration componentOperations = 
		    SciUtil.allMembers(componentClass, true);
		while (componentOperations.hasMoreElements()) {
		    Object element = componentOperations.nextElement();
		    if (!(element instanceof SciOperation)) 
			continue;
		    SciOperation componentOperation = (SciOperation)element;			
		    String pre = componentOperation.getTagList().
			getTagValue("preconditions");
		    String post = componentOperation.getTagList().
			getTagValue("postconditions");
		    if (pre!=null && !"".equals(pre) ||
			post!=null && !"".equals(post)) {
			copySpecVector.addElement(indent+componentOperation.getName());
			addBooleanFieldItem(indent+componentOperation.getName(),false,cond1);
			showItem(indent+componentOperation.getName(),false,cond1);
		    }
		}
	    }

	    addBooleanFieldItem("SimplyDecorated",false);
            inspectorPropertiesVector.addElement("SimplyDecorated");

	    addBooleanFieldItem("Specify Queries",false);
            inspectorPropertiesVector.addElement("Specify Queries");
	    cond2=new MyCondition();

	    queryVector=new Vector();
	    SciClass selectedClass = getSelectedClass();
	    if (selectedClass!=null){
		Enumeration operations = 
		    SciUtil.allMembers(selectedClass, true);
		while (operations.hasMoreElements()) {
		    Object element = operations.nextElement();
		    if (!(element instanceof SciOperation)) 
			continue;
		    SciOperation op = (SciOperation)element;			
		    String query = op.getTagList().
			getTagValue("stereotype");
		    if ("query".equals(query)) {
			// in the following +" " avoids a name clash if 
			// there has already been created a BooleanFieldItem 
			// with the same name
			queryVector.addElement(indent+op.getName()+" ");
			addBooleanFieldItem(indent+op.getName()+" ",false,cond2);
			showItem(indent+op.getName()+" ",false,cond2);
		    }
		}
	    }
 
            myUIBuilder.setCreatedPatternUI();
            myUIBuilder.assignListenedInspectorProperties(inspectorPropertiesVector);

	    //---------------------------------------------------------------
	    addToPropertiesVector(inspectorPropertiesVector);
	    //---------------------------------------------------------------

        }
        catch (PatternBaseException ex) {
            myUIBuilder = null;
            getIdeInspector().clear();
            return;
        }
    }

    protected void assignActivityResponse() {

	getProperties().addPropertyMapListener("Copy spec from methods",
					       new PropertyMapListener() {
		boolean flag=false;
		public void propertiesChanged(PropertyMapEvent event){
		    if (flag)
			flag=false;
		    else
			flag=true;
		    for (int i=0; i<copySpecVector.size(); i++)
			showItem(copySpecVector.elementAt(i).toString(),flag,cond1);
		}
	    }); 

	getProperties().addPropertyMapListener("Specify Queries", 
					       new PropertyMapListener() {
		boolean flag=false;
		public void propertiesChanged(PropertyMapEvent event){
		    if (flag)
			flag=false;
		    else
			flag=true;
		    for (int i=0; i<queryVector.size(); i++)
			showItem(queryVector.elementAt(i).toString(),flag,cond2);		    
		}
	    }); 
  
	       
        getProperties().addPropertyMapListener(SELECTED_CLASS_ROLE, new PropertyMapListener() {
		// class PropertyMapListener
		public void propertiesChanged(PropertyMapEvent event) {
		    String role = getStringPropertyValue(SELECTED_CLASS_ROLE);
		    SciClass componentClass = null;
		    SciClass decoratorClass = null;
		    if (role != null) {
			if (role.equals(LOCAL_COMPONENT)) {
			    componentClass = getSelectedClass();
			    decoratorClass = SciPatternUtil.findPatternLinkSupplier(componentClass, PATTERN_NAME, DECORATOR);
			}
			else if (role.equals(DECORATOR)) {
			    decoratorClass = getSelectedClass();
			    componentClass = findComponentByDecorator(decoratorClass);
			}
			else if (role.equals(CONCRETE_COMPONENT)) {
			    componentClass = SciPatternUtil.findExtendedPatternLinkClient(getSelectedClass(), PATTERN_NAME, CONCRETE_COMPONENT);
			    if (componentClass == null) {
				setPropertyValue(CONCRETE_COMPONENT, null);
				addPropertyValue(CONCRETE_COMPONENT, getSelectedClass().getQualifiedName());
			    }
			    else {
				decoratorClass = SciPatternUtil.findPatternLinkSupplier(componentClass, PATTERN_NAME, DECORATOR);
			    }
			}
			else if (role.equals(CONCRETE_DECORATOR)) {
			    decoratorClass = SciPatternUtil.findExtendedPatternLinkClient(getSelectedClass(), PATTERN_NAME, CONCRETE_DECORATOR);
			    if (decoratorClass == null) {
				setPropertyValue(CONCRETE_DECORATOR, null);
				addPropertyValue(CONCRETE_DECORATOR, getSelectedClass().getQualifiedName());
			    }
			    else {
				componentClass = findComponentByDecorator(decoratorClass);
			    }
			}
		    }
		    
		    if (decoratorClass != null) {
			setPropertyValue(INITIALIZATION_VARIANT, KEY_NONE);
			enableItem(INITIALIZATION_VARIANT, false);
			setPropertyValue(DECORATOR, decoratorClass.getQualifiedName());
		    }
		    else {
			enableItem(INITIALIZATION_VARIANT, true);
		    }
		    
		    if (componentClass != null) {
			setPropertyValue(LOCAL_COMPONENT, componentClass.getQualifiedName());
		    }
		    
		    Enumeration concreteComponentEnumeration = SciPatternUtil.findPatternLinkSuppliers(componentClass, PATTERN_NAME, CONCRETE_COMPONENT);
		    if (concreteComponentEnumeration.hasMoreElements()) {
			setPropertyValue(CONCRETE_COMPONENT, null);
			while (concreteComponentEnumeration.hasMoreElements()) {
			    addPropertyValue(CONCRETE_COMPONENT, ((SciClass)concreteComponentEnumeration.nextElement()).getQualifiedName());
			}
		    }
		    
		    Enumeration concreteDecoratorEnumeration = SciPatternUtil.findPatternLinkSuppliers(decoratorClass, PATTERN_NAME, CONCRETE_DECORATOR);
		    if (concreteDecoratorEnumeration.hasMoreElements()) {
			setPropertyValue(CONCRETE_DECORATOR, null);
			while (concreteDecoratorEnumeration.hasMoreElements()) {
			    addPropertyValue(CONCRETE_DECORATOR, ((SciClass)concreteDecoratorEnumeration.nextElement()).getQualifiedName());
			}
		    }
		    
		    SciAttribute attribute = SciPatternUtil.findAttribute(decoratorClass, componentClass);
		    if (attribute != null) {
			setPropertyValue(ATTRIBUTE, attribute.getName());
		    }
		}
	    });
    }
    
    private PatternUIBuilder    myUIBuilder = null;
    private Vector              myClassRoleVector = new Vector();
    
    private static final String DECORATOR           = "Decorator";
    private static final String LOCAL_COMPONENT           = "Component";
    private static final String CONCRETE_DECORATOR  = "Concrete decorators";
    private static final String CONCRETE_COMPONENT  = "Concrete components";
    private final static String indent = "  -->";
}
