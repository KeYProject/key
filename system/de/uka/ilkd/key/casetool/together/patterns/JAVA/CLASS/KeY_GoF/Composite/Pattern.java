// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together.patterns.JAVA.CLASS.KeY_GoF.Composite;

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
import de.uka.ilkd.key.casetool.together.patterns.HelperClasses.MyPatternBase.MyPatternBaseException;


public class Pattern extends KeyPattern {

    private static final String PATTERN_NAME = "Composite";

    public Pattern() {
        setPatternDisplayName(PATTERN_NAME);
    }

    protected void finalize1() throws Throwable {
        // super.finalize();
	superFinalizeSimu();
        if (myUIBuilder != null) {
            myUIBuilder.removeAllListenedInspectorProperties();
            myUIBuilder = null;
        }
        myClassRoleVector.removeAllElements();
        myClassRoleVector = null;
    }

    public boolean prepare1() {
       	try {
	    // super.prepare();
	    superPrepareSimu();
	    implementedForJavaOnly();

	    setPropertyValue(SELECTED_CLASS_ROLE, null);
            setPropertyValue(LOCAL_COMPONENT, LOCAL_COMPONENT);
            setPropertyValue(LEAF, null);
            setPropertyValue(COMPOSITE, COMPOSITE);
            setPropertyValue(ATTRIBUTE_VECTOR, SciPatternUtil.decapitalize(LOCAL_COMPONENT) + VECTOR);
            setPropertyValue(GET_ENUMERATION_METHOD, SciPatternUtil.decapitalize(LOCAL_COMPONENT) + "s");
            setPropertyValue(ADD_COMPOSITE_OPERATIONS, Boolean.FALSE);
	    // my extension
	    setPropertyValue("Supplier Role","children");
	    setPropertyValue("flavour","strong");
            
	    setPropertyValue(EXPORT_DOCUMENTATION, Boolean.FALSE);
            setPropertyValue(CREATE_PATTERN_LINKS, Boolean.TRUE);

            myGetEnumerationMethodNameChanged = false;
            myAttributeVectorNameChanged = false;

            myClassRoleVector.removeAllElements();

            if (getSelectedClass() == null) {
                addPropertyValue(LEAF, LEAF);
            }
            else {
                // Fill class roles
                myClassRoleVector.addElement(LOCAL_COMPONENT);
                if (!getSelectedClass().hasProperty(SciProperty.INTERFACE)) {
                    myClassRoleVector.addElement(LEAF);
                    myClassRoleVector.addElement(COMPOSITE);
                }

                String currentRole = null;
                if (SciPatternUtil.findExtendedPatternLinkClient(getSelectedClass(), PATTERN_NAME, LEAF) != null) {
                    currentRole = LEAF;
                    addPropertyValue(LEAF, getSelectedClass().getQualifiedName());
                }
                else if (SciPatternUtil.findExtendedPatternLinkClient(getSelectedClass(), PATTERN_NAME, COMPOSITE) != null) {
                    currentRole = COMPOSITE;
                    setPropertyValue(COMPOSITE, getSelectedClass().getQualifiedName());
                }
                else {
                    currentRole = LOCAL_COMPONENT;
                    setPropertyValue(LOCAL_COMPONENT, getSelectedClass().getQualifiedName());
                }
                setPropertyValue(SELECTED_CLASS_ROLE, currentRole);
            }

            initializeInspector();
            assignActivityResponse();
	    //----------------------------------------------------------------

	    initPattern();
 	    //----------------------------------------------------------------
	    //IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "BIN JETZT AM ENDE VON prepare\n");	    
            return true;
      	}
	catch(PatternBaseException e) {
	    System.out.println(e);
            return false;
	    }
    }

    public boolean canApply1() {
        try {
	    //	    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "BIN JETZT AM ANFANG VON canApply()\n");
            String componentName = classNameShouldBeCorrect(LOCAL_COMPONENT);
            SciClass componentClass = findClassByName(componentName);
            shouldBeWritable(LOCAL_COMPONENT, componentClass);

            String compositeName = classNameShouldBeCorrect(COMPOSITE);
            SciClass compositeClass = findClassByName(compositeName);
            cannotBeAnInterface(COMPOSITE, compositeClass);
            shouldBeWritable(COMPOSITE, compositeClass);

            String attributeVectorName = identifierShouldBeCorrect(ATTRIBUTE_VECTOR);
            checkAttributeName(attributeVectorName, compositeClass, VECTOR_FULL_NAME);

            if (compositeClass != null) {
                String getEnumerationMethodName = identifierShouldBeCorrect(GET_ENUMERATION_METHOD);
                SciOperation operation = getFactory().newOperation();
                operation.setName(getEnumerationMethodName);
                SciOperation compositeOperation = (SciOperation)SciUtil.findMemberBySignature(compositeClass, operation);
                checkReturnType(compositeOperation, ENUMERATION_FULL_NAME);
            }

            if (componentClass != null) {
                shouldExtend(compositeClass, componentClass);
            }

            Enumeration enumeration = propertiesEnumeration(LEAF);
            while (enumeration.hasMoreElements()) {
                String leafName = classNameShouldBeCorrect((Property)enumeration.nextElement());
                if (leafName == null || leafName.length() == 0) {
                    continue;
                }
                SciClass leafClass = findClassByName(leafName);
                cannotBeAnInterface(LEAF, leafClass);
                shouldBeWritable(LEAF, leafClass);
                if (componentClass != null) {
                    shouldExtend(leafClass, componentClass);
                }
            }
	    //    IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "BIN JETZT AM ENDE VON canApply()\n");
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
        // super.apply();
	superApplySimu();

        String attributeVectorName = getStringPropertyValue(ATTRIBUTE_VECTOR);
        String getEnumerationMethodName = getStringPropertyValue(GET_ENUMERATION_METHOD);
        boolean addCompositeOperations = getBooleanPropertyValue(ADD_COMPOSITE_OPERATIONS);
	// my extension
	String supplierName = (String)getProperties().getPropertyValue("Supplier Role");


/* Get or create Component class. */

        String componentName = getStringPropertyValue(LOCAL_COMPONENT);
        SciClass componentClass = getClassByName(componentName, true);
        componentClass.setProperty(SciProperty.ABSTRACT, true);

/* Get or create Composite class. Create attribute for Component vector. */

        String compositeName = getStringPropertyValue(COMPOSITE);
        SciClass compositeClass = getClassByName(compositeName, false);
        SciPatternUtil.createInheritance(compositeClass, componentClass);
        // create aggregation link
        //SciAttribute attribute = SciPatternUtil.createVectorAttribute(compositeClass, componentClass, attributeVectorName, true);
	SciAttribute recursiveLink = getFactory().newAttribute();
	recursiveLink.getTagList().setTagValue("associates",componentName);
	recursiveLink.getTagList().setTagValue("link","aggregation");
	recursiveLink.getTagList().setTagValue("supplierCardinality","*");
	recursiveLink.getTagList().setTagValue("supplierRole", supplierName);
	recursiveLink.setName("Enumeration");
	recursiveLink.getType().setText("Vector");
	recursiveLink.setProperty(SciProperty.PRIVATE, true);
	compositeClass.paste(recursiveLink, null, false);

//        try {
            String code = null;

/* Get or create getComposite operation. */

//             SciOperation getCompositeOperation = getFactory().newOperation();
//             getCompositeOperation.setName(GET_COMPOSITE);
//             getCompositeOperation.getReturnType().setReferencedElement(compositeClass);
//             if (SciUtil.findMemberBySignature(componentClass, getCompositeOperation) == null) {
//                 getCompositeOperation.setProperty(SciProperty.ABSTRACT, true);
//                 componentClass.paste(getCompositeOperation, null, false);
//             }
//             if (SciUtil.findMemberBySignature(compositeClass, getCompositeOperation) == null) {
//                 getCompositeOperation.setProperty(SciProperty.ABSTRACT, false);
//                 code = "return this;\n";
//                 getCompositeOperation.setBody(getGenericFactory().newCodeBlock(code));
//                 compositeClass.paste(getCompositeOperation, null, false);
//             }

/* Create sample operation, if all classes are new. */

            if (myAllClassesAreNew) {
                SciOperation sampleOperation = getFactory().newOperation();
                sampleOperation.setName(SAMPLE_OPERATION);
                componentClass.paste(sampleOperation, null, false);
            }

/* Create operations in Composite class. */

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

// 		SciOperation compositeOperation = (SciOperation)SciUtil.findMemberBySignature(compositeClass, componentOperation);
//                 if (compositeOperation != null) {
//                     continue;
//                 }
//                 compositeOperation = (SciOperation)compositeClass.paste(componentOperation, null, false);
//                 if (!exportDocumentation()) {
//                     SciTagEnumeration tags = compositeOperation.getTagList().tags();
//                     while (tags.hasMoreElements()) {
//                         tags.nextSciTag().setValue(null);
//                     }
//                 }
//                 compositeOperation.setProperty(SciProperty.ABSTRACT, false);
//                 if (!VOID.equals(compositeOperation.getReturnType().getText())) {
//                     SciPatternUtil.makeStubImplementation(compositeOperation);
//                 }

//                 String parameters = null;
//                 SciParameterEnumeration parametersEnum = compositeOperation.getParameterList().parameters();
//                 while (parametersEnum.hasMoreElements()) {
//                     parameters += parametersEnum.nextSciParameter().getName();
//                     if (parametersEnum.hasMoreElements()) {
//                         parameters += ", ";
//                     }
//                 }

//                 code =
//                     ENUMERATION_FULL_NAME + " enumeration = " + getEnumerationMethodName + "();\n" +
//                     "while (enumeration.hasMoreElements()) {\n" +
//                     "((" + componentClass.getName() + ")enumeration.nextElement())." +
//                     compositeOperation.getName() + "(" + parameters + ");\n" + "}\n";
//                 // add former operation body
//                 code += compositeOperation.getBody().getText();
//                 compositeOperation.setBody(getGenericFactory().newCodeBlock(code));
             }

	    // my extension
	    // create sample operation
	    SciOperation sampleOperation1 = getFactory().newOperation();
	    sampleOperation1.setName(SAMPLE_OPERATION); 
	    compositeClass.paste(sampleOperation1, null, false);

/* Create Add and Remove methods. */

//             SciOperation operation = getFactory().newOperation();
//             SciParameter parameter = getFactory().newParameter();
//             String parameterName = SciPatternUtil.decapitalize(componentName);

//             parameter.setName(parameterName);
//             parameter.getType().setReferencedElement(componentClass);
//             operation.getParameterList().paste(parameter, null, false);

//             operation.setName(ADD);
//             code = /*"this." + */attributeVectorName + ".addElement(" + parameterName + ");\n";
//             operation.setBody(getGenericFactory().newCodeBlock(code));
//             if (SciUtil.findMemberBySignature(compositeClass, operation) == null) {
//                 compositeClass.paste(operation, null, false);
//             }
//             if (addCompositeOperations && SciUtil.findMemberBySignature(componentClass, operation) == null) {
//                 SciOperation componentOperation = (SciOperation) componentClass.paste(operation, null, false);
//                 if (!componentClass.hasProperty(SciProperty.INTERFACE)) {
//                     SciPatternUtil.makeStubImplementation(componentOperation);
//                 }
//             }

//             operation.setName(REMOVE);
//             code = /*"this." + */attributeVectorName + ".removeElement(" + parameterName + ");\n";
//             operation.setBody(getGenericFactory().newCodeBlock(code));
//             if (SciUtil.findMemberBySignature(compositeClass, operation) == null) {
//                 compositeClass.paste(operation, null, false);
//             }
//             if (addCompositeOperations && SciUtil.findMemberBySignature(componentClass, operation) == null) {
//                 SciOperation componentOperation = (SciOperation)componentClass.paste(operation, null, false);
//                 if (!componentClass.hasProperty(SciProperty.INTERFACE)) {
//                     SciPatternUtil.makeStubImplementation(componentOperation);
//                 }
//             }

/* Create getEnumeration method. */

//             SciOperation getOperation = getFactory().newOperation();
//             getOperation.setName(getEnumerationMethodName);
//             code = "return " + attributeVectorName + ".elements();\n";
//             getOperation.setBody(getGenericFactory().newCodeBlock(code));
//             getOperation.getReturnType().setText(ENUMERATION_FULL_NAME);
//             if (SciUtil.findMemberBySignature(compositeClass, getOperation) == null) {
//                 compositeClass.paste(getOperation, null, false);
//             }

//             if (addCompositeOperations && SciUtil.findMemberBySignature(componentClass, getOperation) == null) {
//                 SciOperation componentOperation = (SciOperation)componentClass.paste(getOperation, null, false);
//                 if (!componentClass.hasProperty(SciProperty.INTERFACE)) {
//                     SciPatternUtil.makeStubImplementation(componentOperation);
//                 }
//             }

/* Create leafs (component implementors). */

            Enumeration enumeration = propertiesEnumeration(LEAF);
            while (enumeration.hasMoreElements()) {
                String leafName = (String)((Property)enumeration.nextElement()).getValue();
                if (leafName == null || leafName.length() == 0) {
                    continue;
                }
                SciClass leafClass = getClassByName(leafName, false);
                SciPatternUtil.makeStubImplementation(leafClass, componentClass, false, exportDocumentation());
//                 if (createPatternLinks()) {
//                     SciPatternUtil.addPatternLink(componentClass, leafClass, PATTERN_NAME, null, LEAF, false);
//                 }
            }

/* Create pattern link. */

//             if (createPatternLinks()) {
//                 //addPatternLink(SciClass source, SciClass target, String patternName,
//                 //  String clientRole, String supplierRole, boolean hidden)
//                 SciPatternUtil.addPatternLink(componentClass, compositeClass, PATTERN_NAME, null, COMPOSITE, false);
//             }
//         }
//         catch(SciGenericFactoryException e) {
//             return;
//         }
	//----------------------------------------------------------------
        applyOCLSchemes();
	//----------------------------------------------------------------
    }

    private SciClass findComponentByComposite(SciClass composite) {
        if (composite == null) {
            return null;
        }

        Enumeration inheritances = composite.getExtendsList().inheritances();
        while (inheritances.hasMoreElements()) {
            SciClass component = (SciClass)((SciInheritance)inheritances.
                    nextElement()).getReferencedElement();
            if (component != null) {
                Enumeration attributes = composite.attributes();
                while (attributes.hasMoreElements()) {
                    SciAttribute attribute = (SciAttribute) attributes.nextElement();
                    String attributeClassName = attribute.getType().getText();
                    if (VECTOR.equals(attributeClassName) || VECTOR_FULL_NAME.equals(attributeClassName)) {
                        SciTag tag = attribute.getTagList().getTag(ASSOCIATES);
                        if (component.equals(tag.getValueAsReference().getReferencedElement())) {
                            return component;
                        }
                    }
                }
            }
        }

        if (SciLanguage.JAVA.equals(getLanguage()) && !composite.hasProperty(SciProperty.INTERFACE)) {
            inheritances = composite.getImplementsList().inheritances();
            while (inheritances.hasMoreElements()) {
                SciClass component = (SciClass)((SciInheritance)inheritances.nextElement()).getReferencedElement();
                if (component != null) {
                    Enumeration attributes = composite.attributes();
                    while (attributes.hasMoreElements()) {
                        SciAttribute attribute = (SciAttribute) attributes.nextElement();
                        String attributeClassName = attribute.getType().getText();
                        if (VECTOR.equals(attributeClassName) || VECTOR_FULL_NAME.equals(attributeClassName)) {
                            SciTag tag = attribute.getTagList().getTag(ASSOCIATES);
                            if (component.equals(tag.getValueAsReference().getReferencedElement())) {
                                return component;
                            }
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
            String pageName1 = "Pattern properties";
	    if (myUIBuilder.addInspectorPage(pageName1, PatternUIBuilder.UIPresentation.Table) == null) {
                throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }

       	    //----------------------------------------------------------------
	    setUIBuilder(myUIBuilder);
	    setPageName(pageName1);
	    //----------------------------------------------------------------

            // Add SELECTED_CLASS_ROLE property
            if (getStringPropertyValue(SELECTED_CLASS_ROLE) != null) {
                if (myUIBuilder.addPropertyToPage(pageName1, SELECTED_CLASS_ROLE, SELECTED_CLASS_ROLE,
                    PatternUIBuilder.PropertyType.StringChooser, myClassRoleVector.toArray()) == null) {
                    throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
                }
                inspectorPropertiesVector.addElement(SELECTED_CLASS_ROLE);
            }
	    
	    	    
            // Add LOCAL_COMPONENT property
            boolean allowInterface = true;
            if (myUIBuilder.addClassPropertyToPage(pageName1, LOCAL_COMPONENT, LOCAL_COMPONENT,
                PatternUIBuilder.PropertyType.SingleValue, allowInterface) == null) {
                throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(LOCAL_COMPONENT);

	    // Add LEAF property
            allowInterface = false;
            if (myUIBuilder.addClassPropertyToPage(pageName1, LEAF, LEAF,
                PatternUIBuilder.PropertyType.MultiValue, allowInterface) == null) {
                throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(LEAF);

            // Add COMPOSITE property
            allowInterface = false;
            if (myUIBuilder.addClassPropertyToPage(pageName1, COMPOSITE, COMPOSITE,
                PatternUIBuilder.PropertyType.SingleValue, allowInterface) == null) {
                throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(COMPOSITE);

//             // Add ATTRIBUTE_VECTOR property
//             if (myUIBuilder.addPropertyToPage(pageName1, ATTRIBUTE_VECTOR, ATTRIBUTE_VECTOR,
//                 PatternUIBuilder.PropertyType.String) == null) {
//                 throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
//             }
//             inspectorPropertiesVector.addElement(ATTRIBUTE_VECTOR);

//             // Add GET_ENUMERATION_METHOD property
//             if (myUIBuilder.addPropertyToPage(pageName1, GET_ENUMERATION_METHOD, GET_ENUMERATION_METHOD,
//                 PatternUIBuilder.PropertyType.String) == null) {
//                 throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
//             }
//             inspectorPropertiesVector.addElement(GET_ENUMERATION_METHOD);

//             // Add ADD_COMPOSITE_OPERATIONS property
//             if (myUIBuilder.addPropertyToPage(pageName1, ADD_COMPOSITE_OPERATIONS, ADD_COMPOSITE_OPERATIONS,
//                 PatternUIBuilder.PropertyType.Boolean) == null) {
//                 throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
//             }
//             inspectorPropertiesVector.addElement(ADD_COMPOSITE_OPERATIONS);

//             // Add EXPORT_DOCUMENTATION property
//             if (myUIBuilder.AddExportDocumentationProperty(pageName1) == null) {
//                 throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
//             }
//             inspectorPropertiesVector.addElement(EXPORT_DOCUMENTATION);

//             // Add "Create pattern links" property
//             if (myUIBuilder.AddCreatePatternLinksProperty(pageName1) == null) {
//                 throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
//             }
//             inspectorPropertiesVector.addElement(CREATE_PATTERN_LINKS);
	    
	    // my extension
	    // add a StringField "Supplier Role"
	    // not contained in the Togethersoft version
            if (myUIBuilder.addPropertyToPage(pageName1, "Supplier Role", "Supplier Role",
                PatternUIBuilder.PropertyType.String) == null) {
                throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement("Supplier Role");



            myUIBuilder.setCreatedPatternUI();
            myUIBuilder.assignListenedInspectorProperties(inspectorPropertiesVector);
	    //---------------------------------------------------------------
	    addToPropertiesVector(inspectorPropertiesVector);
	    //---------------------------------------------------------------
        }
        catch (MyPatternBaseException ex) {
            myUIBuilder = null;
            getIdeInspector().clear();
            return;
        }
    }

    protected void assignActivityResponse() {
        addPropertyMapListener(LOCAL_COMPONENT, new PropertyMapListener() {
            public void propertiesChanged(PropertyMapEvent event) {
                if (!myGetEnumerationMethodNameChanged || !myAttributeVectorNameChanged) {
                    String componentName = getStringPropertyValue(LOCAL_COMPONENT);
                    if (componentName == null) {
                        componentName = EMPTY_STRING;
                    }
                    componentName = componentName.substring(componentName.lastIndexOf('.') + 1);
                    if (!myGetEnumerationMethodNameChanged) {
                        setPropertyValue(GET_ENUMERATION_METHOD, SciPatternUtil.decapitalize(componentName) + "s");
                        myGetEnumerationMethodNameChanged = false;
                    }
                    if (!myAttributeVectorNameChanged) {
                        setPropertyValue(ATTRIBUTE_VECTOR, SciPatternUtil.decapitalize(componentName) + VECTOR);
                        myAttributeVectorNameChanged = false;
                    }
                }
            }
        });

        addPropertyMapListener(GET_ENUMERATION_METHOD, new PropertyMapListener() {
            public void propertiesChanged(PropertyMapEvent event) {
                myGetEnumerationMethodNameChanged = true;
		//		IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION, "Event: "+event.toString());
            }
        });

        addPropertyMapListener(ATTRIBUTE_VECTOR, new PropertyMapListener() {
            public void propertiesChanged(PropertyMapEvent event) {
                myAttributeVectorNameChanged = true;
            }
        });

        addPropertyMapListener(SELECTED_CLASS_ROLE, new PropertyMapListener() {
            public void propertiesChanged(PropertyMapEvent event) {
                String role = getStringPropertyValue(SELECTED_CLASS_ROLE);
                SciClass componentClass = null;
                SciClass compositeClass = null;
                if (role != null) {
                    if (role.equals(LOCAL_COMPONENT)) {
                        componentClass = getSelectedClass();
                        compositeClass = SciPatternUtil.findPatternLinkSupplier(componentClass, PATTERN_NAME, COMPOSITE);
                    }
                    else if (role.equals(COMPOSITE)) {
                        compositeClass = getSelectedClass();
                        componentClass = findComponentByComposite(compositeClass);
                    }
                    else if (role.equals(LEAF)) {
                        componentClass = SciPatternUtil.findExtendedPatternLinkClient(getSelectedClass(), PATTERN_NAME, LEAF);
                        if (componentClass == null) {
                            setPropertyValue(LEAF, null);
                            addPropertyValue(LEAF, getSelectedClass().getQualifiedName());
                        }
                        else {
                            compositeClass = SciPatternUtil.findPatternLinkSupplier(componentClass, PATTERN_NAME, COMPOSITE);
                        }
                    }
                }

                if (compositeClass != null) {
                    setPropertyValue(COMPOSITE, compositeClass.getQualifiedName());
                }
                if (componentClass != null) {
                    setPropertyValue(LOCAL_COMPONENT, componentClass.getQualifiedName());
                }

                Enumeration leafEnumeration = SciPatternUtil.findPatternLinkSuppliers(componentClass, PATTERN_NAME, LEAF);
                if (leafEnumeration.hasMoreElements()) {
                    setPropertyValue(LEAF, null);
                    while (leafEnumeration.hasMoreElements()) {
                        addPropertyValue(LEAF, ((SciClass)leafEnumeration.nextElement()).getQualifiedName());
                    }
                }
                if (compositeClass != null && componentClass != null) {
                    SciAttribute attribute = SciPatternUtil.findVectorAttribute(compositeClass, componentClass);
                    if (attribute != null) {
                        setPropertyValue(ATTRIBUTE_VECTOR, attribute.getName());
                    }
                    Enumeration operations = compositeClass.operations();
                    while (operations.hasMoreElements()) {
                        SciOperation operation = (SciOperation) 
                            operations.nextElement();
                        String returnType = operation.getReturnType().getText();
                        if (ENUMERATION.equals(returnType) || ENUMERATION_FULL_NAME.equals(returnType)) {
                            setPropertyValue(GET_ENUMERATION_METHOD, operation.getName());
                            break;
                        }
                    }
                }
            }
        });
    }

    private PatternUIBuilder    myUIBuilder = null;
    private Vector              myClassRoleVector = new Vector();

    private boolean myGetEnumerationMethodNameChanged;
    private boolean myAttributeVectorNameChanged;

    private static final String COMPOSITE           = "Composite";
    private static final String LOCAL_COMPONENT     = "Component";
    private static final String LEAF                = "Leaf";
    private static final String ATTRIBUTE_VECTOR    = "Attribute vector";
    private static final String ASSOCIATES          = "associates";
    private static final String GET_ENUMERATION_METHOD = "getEnumeration method";
    private static final String ADD_COMPOSITE_OPERATIONS = "Add composite operations to component";
    // Operation names
    private static final String GET_COMPOSITE       = "getComposite";
    private static final String SAMPLE_OPERATION    = "sampleOperation";
    private static final String ADD                 = "add";
    private static final String REMOVE              = "remove";
}
