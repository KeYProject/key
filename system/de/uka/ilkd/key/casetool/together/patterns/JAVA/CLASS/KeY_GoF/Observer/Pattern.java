// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together.patterns.JAVA.CLASS.KeY_GoF.Observer;

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

    private static final String PATTERN_NAME = "Observer";

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

        myUpdateOperation = null;
        myAttachOperation = null;
        myDetachOperation = null;
        myNotifyOperation = null;
    }

    public boolean prepare1()
    {
        try {
            //super.prepare();
	    superPrepareSimu();
            notImplementedForIDL();

           // PropertyMap initialization
            setPropertyValue(SELECTED_CLASS_ROLE, null);
            setPropertyValue(LOCAL_SUBJECT, LOCAL_SUBJECT);
            setPropertyValue(OBSERVER, OBSERVER);
            setPropertyValue(CONCRETE_SUBJECT, null);
            setPropertyValue(CONCRETE_OBSERVER, null);
            setPropertyValue(EXPORT_DOCUMENTATION, Boolean.FALSE);
            setPropertyValue(CREATE_PATTERN_LINKS, Boolean.TRUE);
	    // my extension
	    setPropertyValue("Supplier Role of association state","state");
	    setPropertyValue("Supplier Role of association observers","observer");
	

            myClassRoleVector.removeAllElements();

            if (getSelectedClass() == null) {
                addPropertyValue(CONCRETE_SUBJECT, CONCRETE + LOCAL_SUBJECT);
                addPropertyValue(CONCRETE_OBSERVER, CONCRETE + OBSERVER);
            }
            else {
                // Create pattern for existed class
                myClassRoleVector.addElement(LOCAL_SUBJECT);
                myClassRoleVector.addElement(OBSERVER);
                myClassRoleVector.addElement(CONCRETE_OBSERVER);
                if (!getSelectedClass().hasProperty(SciProperty.INTERFACE)) {
                    myClassRoleVector.insertElementAt(CONCRETE_SUBJECT, 1);
                }

                String currentRole = EMPTY_STRING;
                if (SciPatternUtil.findPatternLinkSupplier(getSelectedClass(), PATTERN_NAME, LOCAL_SUBJECT) != null) {
                    currentRole = OBSERVER;
                }
                else if (SciPatternUtil.findExtendedPatternLinkClient(getSelectedClass(), PATTERN_NAME, CONCRETE_SUBJECT) != null) {
                    currentRole = CONCRETE_SUBJECT;
                }
                else if (SciPatternUtil.findExtendedPatternLinkClient(getSelectedClass(), PATTERN_NAME, CONCRETE_OBSERVER) != null) {
                    currentRole = CONCRETE_OBSERVER;
                }
                else {
                    currentRole = LOCAL_SUBJECT;
                }

                setPropertyValue(SELECTED_CLASS_ROLE, currentRole);
            }

            initializeInspector();
            assignActivityResponse();
	    //----------------------------------------------------------------

	    initPattern();
 	    //----------------------------------------------------------------
            return true;
        }
        catch(PatternBaseException e) {
            return false;
        }
    }

    public boolean canApply1() {
        try {
            String observerName = classNameShouldBeCorrect(OBSERVER);
            SciClass observerClass = findClassByName(observerName);
            shouldBeWritable(OBSERVER, observerClass);
            checkConcreteElements(observerClass, CONCRETE_OBSERVER, true);

            String subjectName = classNameShouldBeCorrect(LOCAL_SUBJECT);
            SciClass subjectClass = findClassByName(subjectName);
            shouldBeWritable(LOCAL_SUBJECT, subjectClass);
            checkConcreteElements(subjectClass, CONCRETE_SUBJECT, false);

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
	
//         try {
            String subjectName = getStringPropertyValue(LOCAL_SUBJECT);
            String observerName = getStringPropertyValue(OBSERVER);
            String shortObserverName = observerName.substring(observerName.lastIndexOf(".") + 1);

            SciClass subjectClass = getClassByName(subjectName, true);
            subjectClass.setProperty(SciProperty.ABSTRACT, true);

            SciClass observerClass = getClassByName(observerName, true);
            observerClass.setProperty(SciProperty.ABSTRACT, true);

/* Create "update" operation if is not exists */
            myUpdateOperation = getFactory().newOperation();
            myUpdateOperation.setName(UPDATE_METHOD);
            if (SciUtil.findMemberBySignature(observerClass, myUpdateOperation) == null) {
                // paste if this operation is not exist
                myUpdateOperation = (SciOperation) observerClass.paste(myUpdateOperation, null, false);
                myUpdateOperation.setProperty(SciProperty.ABSTRACT, true);
            }

            SciParameter observerParameter = getFactory().newParameter();
            observerParameter.setName(SciPatternUtil.decapitalize(shortObserverName));
            observerParameter.getType().setReferencedElement(observerClass);
            observerParameter.setType( getLanguageHelper().makePointerType(observerParameter.getType()) );

// /* Create "attach" operation */
//             myAttachOperation = getFactory().newOperation();
//             myAttachOperation.setName(ATTACH_METHOD);
//             myAttachOperation.getParameterList().paste(observerParameter, null, false);
//             if (SciUtil.findMemberBySignature(subjectClass, myAttachOperation) == null) {
//                 SciOperation op = (SciOperation) subjectClass.paste(myAttachOperation, null, false);
//                 op.setProperty(SciProperty.ABSTRACT, true);
//             }
// /* Create "detach" operation */
//             myDetachOperation = getFactory().newOperation();
//             myDetachOperation.setName(DETACH_METHOD);
//             myDetachOperation.getParameterList().paste(observerParameter, null, false);
//             if (SciUtil.findMemberBySignature(subjectClass, myDetachOperation) == null) {
//                 SciOperation op = (SciOperation) subjectClass.paste(myDetachOperation, null, false);
//                 op.setProperty(SciProperty.ABSTRACT, true);
//             }

// /* Create "inform" operation */
//             myNotifyOperation = getFactory().newOperation();
//             myNotifyOperation.setName(NOTIFY_METHOD);
//             if (SciUtil.findMemberBySignature(subjectClass, myNotifyOperation) == null) {
//                 SciOperation op = (SciOperation) subjectClass.paste(myNotifyOperation, null, false);
//                 op.setProperty(SciProperty.ABSTRACT, true);
//             }

//             try {
	         String observer = SciPatternUtil.decapitalize(shortObserverName);
//                 String body = EMPTY_STRING;

                 String attributeName = generateAttributeName(observer);

//                 // Generate body of the observers operation
//                 SciOperation observersOperation = getFactory().newOperation();
//                 observersOperation.setName(observer + "s");

//                 observersOperation.getReturnType().setText( generateReturnedContainerType(shortObserverName) );
//                 observersOperation.setReturnType( getLanguageHelper().makeReferenceType(observersOperation.getReturnType()) );


//                 body = generateObserversOperationBody(attributeName);
//                 observersOperation.setBody( getGenericFactory().newCodeBlock(body) );

//                 // Generate body of the attach operation
//                 body = generateAttachOperationBody(attributeName, observerParameter.getName());
//                 myAttachOperation.setBody( getGenericFactory().newCodeBlock(body) );

//                 // Generate body of the detach operation
//                 body = generateDetachOperationBody(attributeName, observerParameter.getName());
//                 myDetachOperation.setBody( getGenericFactory().newCodeBlock(body) );

//                 // Generate body of the notify operation
//                 body = generateNotifyOperationBody(shortObserverName, observersOperation.getName());
//                 myNotifyOperation.setBody( getGenericFactory().newCodeBlock(body) );

                SciClass concreteSubjectClass = null;
                Enumeration subjects = propertiesEnumeration(CONCRETE_SUBJECT);
                while (subjects.hasMoreElements()) {
                    String concreteSubjectName = (String)((Property)subjects.nextElement()).getValue();
                    if (concreteSubjectName == null || concreteSubjectName.length() == 0) {
                        continue;
                    }

                    concreteSubjectClass = getClassByName(concreteSubjectName, false);

//                     // create pattern links
//                     if (createPatternLinks()) {
//                         SciPatternUtil.addPatternLink(subjectClass, concreteSubjectClass, PATTERN_NAME, null, CONCRETE_SUBJECT, false);
//                     }

                    SciPatternUtil.createInheritance(concreteSubjectClass, subjectClass);

                    // create attribute
//                     SciAttribute attribute = null;
//                     attribute = SciPatternUtil.createVectorAttribute(concreteSubjectClass, observerClass, attributeName, false);
//                     if (SciLanguage.CPP.equals(getLanguage())) {
//                         attribute.getType().setText( generateListAttributeForCPP(shortObserverName) );
//                     }

//                     // paste Attach operation
//                     if (SciUtil.findMemberBySignature(concreteSubjectClass, myAttachOperation) == null) {
//                         concreteSubjectClass.paste(myAttachOperation, null, false);
//                     }

//                     // paste Detach operation
//                     if (SciUtil.findMemberBySignature(concreteSubjectClass, myDetachOperation) == null) {
//                         concreteSubjectClass.paste(myDetachOperation, null, false);
//                     }
//                     // paste Notify operation
//                     if (SciUtil.findMemberBySignature(concreteSubjectClass, myNotifyOperation) == null) {
//                         concreteSubjectClass.paste(myNotifyOperation, null, false);
//                     }
                    // paste Observers operation
 //                     if (SciUtil.findMemberBySignature(concreteSubjectClass, observersOperation) == null) {
//                         concreteSubjectClass.paste(observersOperation, null, false);
//                     }
                }
//             }
//             catch(SciGenericFactoryException e) {
//                 throw new MyPatternBaseException(CODE_GENERATION_ERROR);
//             }

            String concreteObserverName = null;
            SciClass concreteObserverClass = null;
            Enumeration observers = propertiesEnumeration(CONCRETE_OBSERVER);
            while (observers.hasMoreElements()) {
                concreteObserverName = (String) ((Property)observers.nextElement()).getValue();
                if (concreteObserverName == null || concreteObserverName.length() == 0) {
                    continue;
                }

                concreteObserverClass = getClassByName(concreteObserverName, false);
                SciPatternUtil.makeStubImplementation(concreteObserverClass, observerClass, true, exportDocumentation());
//                 if (createPatternLinks()) {
//                     SciPatternUtil.addPatternLink(observerClass, concreteObserverClass, PATTERN_NAME, null, CONCRETE_OBSERVER, false);
//                 }
            }

//             if (createPatternLinks()) {
//                 SciPatternUtil.addPatternLink(observerClass, subjectClass, PATTERN_NAME, OBSERVER, SUBJECT, false);
//                 SciPatternUtil.addPatternLink(subjectClass, observerClass, PATTERN_NAME, null, OBSERVER, true);
//             }

	    // my extension
	    String supplierName = (String) getProperties().getPropertyValue("Supplier Role of association state");	    
	    String observersName = (String)getProperties().getPropertyValue("Supplier Role of association observers");

	    SciClass stateClass = getClassByName("SubjectState", false);

	    SciAttribute associationState = getFactory().newAttribute();
	    associationState.getTagList().setTagValue("associates",stateClass.getUniqueName());
	    associationState.getTagList().setTagValue("link","association");
	    associationState.getTagList().setTagValue("supplierCardinality","1");
	    associationState.getTagList().setTagValue("supplierRole", supplierName);
	    associationState.setProperty(SciProperty.PRIVATE, true);
	    subjectClass.paste(associationState, null, false);
	    
	    SciAttribute association = getFactory().newAttribute();
	    association.getTagList().setTagValue("associates",observerClass.getUniqueName());
	    association.getTagList().setTagValue("link","association");
	    association.getTagList().setTagValue("supplierCardinality","0..*");
	    association.getTagList().setTagValue("supplierRole", observersName);
	    association.setProperty(SciProperty.PRIVATE, true);
	    subjectClass.paste(association, null, false);
	

	    //----------------------------------------------------------------
	    applyOCLSchemes();
	    //----------------------------------------------------------------
//         }
//         catch (PatternBaseException ex) {
//           return;
//         }

        myUpdateOperation = null;
        myAttachOperation = null;
        myDetachOperation = null;
        myNotifyOperation = null;
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

            // Add SUBJECT property
            boolean allowInterface = true;
            if (myUIBuilder.addClassPropertyToPage(pageName1, LOCAL_SUBJECT, LOCAL_SUBJECT,
                PatternUIBuilder.PropertyType.SingleValue, allowInterface) == null) {
                throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(LOCAL_SUBJECT);

            // Add OBSERVER property
            allowInterface = true;
            if (myUIBuilder.addClassPropertyToPage(pageName1, OBSERVER, OBSERVER,
                PatternUIBuilder.PropertyType.SingleValue, allowInterface) == null) {
                throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(OBSERVER);

            // Add CONCRETE_SUBJECT property
            allowInterface = true;
            if (myUIBuilder.addClassPropertyToPage(pageName1, CONCRETE_SUBJECT, CONCRETE_SUBJECT,
                PatternUIBuilder.PropertyType.MultiValue, allowInterface) == null) {
                throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(CONCRETE_SUBJECT);

            // Add CONCRETE_OBSERVER property
            allowInterface = true;
            if (myUIBuilder.addClassPropertyToPage(pageName1, CONCRETE_OBSERVER, CONCRETE_OBSERVER,
                PatternUIBuilder.PropertyType.MultiValue, allowInterface) == null) {
                throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement(CONCRETE_OBSERVER);

	    // my extension
	    if (myUIBuilder.addPropertyToPage(pageName1, "Supplier Role of association state", "Supplier Role of association state",PatternUIBuilder.PropertyType.String) == null) {
                throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement("Supplier Role of association state");

	    // my extension
	    if (myUIBuilder.addPropertyToPage(pageName1, "Supplier Role of association observers", "Supplier Role of association observers",PatternUIBuilder.PropertyType.String) == null) {
                throw new MyPatternBaseException(CANNOT_CREATE_PATTERN_UI);
            }
            inspectorPropertiesVector.addElement("Supplier Role of association observers");


	    

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
        addPropertyMapListener(SELECTED_CLASS_ROLE, new PropertyMapListener() {
            // class PropertyMapListener
            public void propertiesChanged(PropertyMapEvent event) {
                String role = getStringPropertyValue(SELECTED_CLASS_ROLE);
                SciClass subjectClass = null;
                SciClass observerClass = null;

                if (role != null) {
                    if (role.equals(LOCAL_SUBJECT)) {
                        subjectClass = getSelectedClass();
                        observerClass = SciPatternUtil.findPatternLinkSupplier(subjectClass, PATTERN_NAME, OBSERVER);
                    }
                    else if (role.equals(OBSERVER)) {
                        observerClass = getSelectedClass();
                        subjectClass = SciPatternUtil.findPatternLinkSupplier(observerClass, PATTERN_NAME, LOCAL_SUBJECT);
                    }
                    else if (role.equals(CONCRETE_SUBJECT)) {
                        subjectClass = SciPatternUtil.findExtendedPatternLinkClient(getSelectedClass(), PATTERN_NAME, CONCRETE_SUBJECT);
                        if (subjectClass == null) {
                            setPropertyValue(CONCRETE_SUBJECT, null);
                            addPropertyValue(CONCRETE_SUBJECT, getSelectedClass().getQualifiedName());
                        }
                        else {
                            observerClass = SciPatternUtil.findPatternLinkSupplier(subjectClass, PATTERN_NAME, OBSERVER);
                        }
                    }
                    else if (role.equals(CONCRETE_OBSERVER)) {
                        observerClass = SciPatternUtil.findExtendedPatternLinkClient(getSelectedClass(), PATTERN_NAME, CONCRETE_OBSERVER);
                        if (observerClass == null) {
                            setPropertyValue(CONCRETE_OBSERVER, null);
                            addPropertyValue(CONCRETE_OBSERVER, getSelectedClass().getQualifiedName());
                        }
                        else {
                            subjectClass = SciPatternUtil.findPatternLinkSupplier(observerClass, PATTERN_NAME, LOCAL_SUBJECT);
                        }
                    }
                }

                if (observerClass != null) {
                    setPropertyValue(OBSERVER, observerClass.getQualifiedName());
                }
                if (subjectClass != null) {
                    setPropertyValue(LOCAL_SUBJECT, subjectClass.getQualifiedName());
                }

                Enumeration concreteObserverEnumeration =
                    SciPatternUtil.findPatternLinkSuppliers(observerClass, PATTERN_NAME, CONCRETE_OBSERVER);
                if (concreteObserverEnumeration.hasMoreElements()) {
                    setPropertyValue(CONCRETE_OBSERVER, null);
                    while (concreteObserverEnumeration.hasMoreElements()) {
                        addPropertyValue(CONCRETE_OBSERVER, ((SciClass)concreteObserverEnumeration.nextElement()).getQualifiedName());
                    }
                }

                Enumeration concreteSubjectEnumeration =
                    SciPatternUtil.findPatternLinkSuppliers(subjectClass, PATTERN_NAME, CONCRETE_SUBJECT);
                if (concreteSubjectEnumeration.hasMoreElements()) {
                    setPropertyValue(CONCRETE_SUBJECT, null);
                    while (concreteSubjectEnumeration.hasMoreElements()) {
                        addPropertyValue(CONCRETE_SUBJECT, ((SciClass)concreteSubjectEnumeration.nextElement()).getQualifiedName());
                    }
                }

                getIdeInspector().clear();
            }
        });
    }

/* private methods */

    private String generateObserversOperationBody(String attributeName) {
        String codeTemplate = null;
        if (SciLanguage.CPP.equals(getLanguage())) {
            codeTemplate = CPP_OBSERVERS_BODY;
        }
        else {
            codeTemplate = JAVA_OBSERVERS_BODY;
        }

        Object[] arguments = { attributeName };
        return createTextByPattern(codeTemplate, arguments);
    }

    private String generateAttachOperationBody(String attrName, String paramName) {
        String codeTemplate = null;
        if (SciLanguage.CPP.equals(getLanguage())) {
            codeTemplate = CPP_ATTACH_BODY;
        }
        else {
            codeTemplate = JAVA_ATTACH_BODY;
        }

        Object[] arguments = { attrName, paramName };
        return createTextByPattern(codeTemplate, arguments);
    }

    private String generateDetachOperationBody(String attrName, String paramName) {
        String codeTemplate = null;
        if (SciLanguage.CPP.equals(getLanguage())) {
            codeTemplate = CPP_DETACH_BODY;
        }
        else {
            codeTemplate = JAVA_DETACH_BODY;
        }

        Object[] arguments = { attrName, paramName };
        return createTextByPattern(codeTemplate, arguments);
    }

    private String generateNotifyOperationBody(String observerClassName, String observersOperationName) {
        String codeTemplate = null;
        if (SciLanguage.CPP.equals(getLanguage())) {
            codeTemplate = CPP_NOTIFY_BODY;
        }
        else {
            codeTemplate = JAVA_NOTIFY_BODY;
        }
        // 0 - Observer, 1 - observers,
        Object[] arguments = { observerClassName, observersOperationName };
        return createTextByPattern(codeTemplate, arguments);
    }

    private String generateReturnedContainerType(String storedType) {
        String codeTemplate = null;
        if (SciLanguage.CPP.equals(getLanguage())) {
            codeTemplate = CPP_CONTAINER;
        }
        else {
            codeTemplate = JAVA_ITERATOR;
        }

        Object[] arguments = { storedType };
        return createTextByPattern(codeTemplate, arguments);
    }

    private String generateAttributeName(String foreName) {
        String codeTemplate = null;
        if (SciLanguage.CPP.equals(getLanguage())) {
            codeTemplate = CPP_ATTRIBUTE;
        }
        else {
            codeTemplate = JAVA_ATTRIBUTE;
        }

        Object[] arguments = { foreName };
        return createTextByPattern(codeTemplate, arguments);
    }

    private String generateListAttributeForCPP(String storedType) {
        if (!SciLanguage.CPP.equals(getLanguage())) {
            return null;
        }
        else
            return generateReturnedContainerType(storedType);
    }

    private PatternUIBuilder    myUIBuilder = null;
    private Vector              myClassRoleVector = new Vector();

    private SciOperation myUpdateOperation = null;
    private SciOperation myAttachOperation = null;
    private SciOperation myDetachOperation = null;
    private SciOperation myNotifyOperation = null;

    private static final String OBSERVER            = "Observer";
    private static final String LOCAL_SUBJECT             = "Subject";
    private static final String CONCRETE_OBSERVER   = "Concrete observers";
    private static final String CONCRETE_SUBJECT    = "Concrete subjects";
    private static final String CONCRETE            = "Concrete";
    // Operation names
    private static final String ATTACH_METHOD       = "attach";
    private static final String DETACH_METHOD       = "detach";
    private static final String UPDATE_METHOD       = "update";
    private static final String NOTIFY_METHOD       = "notify";

    // Java code patterns
    private static final String JAVA_CONTAINER      = "java.util.Vector";
    private static final String JAVA_ITERATOR       = "java.util.Enumeration";
    private static final String JAVA_ATTRIBUTE      = "{0}sVector";
    private static final String JAVA_ATTACH_BODY    = "\n{0}.addElement({1});\n";
    private static final String JAVA_DETACH_BODY    = "\n{0}.removeElement({1});\n";
    // 0 - Observer, 1 - observers()
    private static final String JAVA_NOTIFY_BODY    = "\n" + JAVA_ITERATOR +" enumeration = {1}(); while (enumeration.hasMoreElements()) '{'\n(({0})enumeration.nextElement()).update();\n'}'\n";
    private static final String JAVA_OBSERVERS_BODY = "\nreturn ((java.util.Vector){0}.clone()).elements();\n";

    // C++ code patterns
    private static final String CPP_CONTAINER       = "list<{0}*>";
    private static final String CPP_ITERATOR        = "list<{0}*>::iterator";
    private static final String CPP_ATTRIBUTE       = "{0}sList";
    private static final String CPP_ATTACH_BODY     = "\n{0}.push_back({1});\n";
    private static final String CPP_DETACH_BODY     = "\n{0}.remove({1});\n";
    private static final String CPP_NOTIFY_BODY     = "\nlist<{0}*>::iterator it = {1}().begin(); while (it != {1}().end()) '{'it->update(); it++;'}'";
    private static final String CPP_OBSERVERS_BODY  = "\nreturn {0};\n";
}
