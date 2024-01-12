/*
 * @(#)DeprecatedAPIListBuilder.java	1.6 00/02/02
 *
 * Copyright 1998-2000 Sun Microsystems, Inc. All Rights Reserved.
 * 
 * This software is the proprietary information of Sun Microsystems, Inc.  
 * Use is subject to license terms.
 * 
 */




import com.sun.tools.doclets.*;
import com.sun.javadoc.*;
import java.io.*;
import java.lang.*;
import java.util.*;

/**
 * Build list of all the deprecated classes, constructors, fields and methods.
 *
 * @author Atul M Dambalkar
 */
public class DeprecatedAPIListBuilder {

    /**
     * List of all the deprecated classes. 
     */ 
    private List deprecatedclasses = new ArrayList();

    /**
     * List of all the deprecated interfaces. 
     */ 
    private List deprecatedinterfaces = new ArrayList();

    /**
     * List of all the deprecated exceptions. 
     */ 
    private List deprecatedexceptions = new ArrayList();

    /**
     * List of all the deprecated errors. 
     */ 
    private List deprecatederrors = new ArrayList();

    /**
     * List of all the deprecated fields. 
     */ 
    private List deprecatedfields = new ArrayList();

    /**
     * List of all the deprecated methods. 
     */ 
    private List deprecatedmethods = new ArrayList();

    /**
     * List of all the deprecated constructors. 
     */ 
    private List deprecatedconstructors = new ArrayList();

    /**
     * Constructor.
     *
     * @param root Root of the tree.
     */
    public DeprecatedAPIListBuilder(RootDoc root) {
        buildDeprecatedAPIInfo(root);
    }

    /**
     * Build the sorted list of all the deprecated APIs in this run. 
     * Build separate lists for deprecated classes, constructors, methods and
     * fields.
     *
     * @param root Root of the tree.
     */
    private void buildDeprecatedAPIInfo(RootDoc root) {
        ClassDoc[] classes = root.classes();
        for (int i = 0; i < classes.length; i++) {
            ClassDoc cd = classes[i];
            if (cd.tags("deprecated").length > 0) {
                if (cd.isOrdinaryClass()) {
                    deprecatedclasses.add(cd);
                } else if (cd.isInterface()) {
                    deprecatedinterfaces.add(cd);
                } else if (cd.isException()) {
                    deprecatedexceptions.add(cd);
                } else {
                    deprecatederrors.add(cd);
                }
            }
            composeDeprecatedList(deprecatedfields, cd.fields());
            composeDeprecatedList(deprecatedmethods, cd.methods());
            composeDeprecatedList(deprecatedconstructors, cd.constructors());
        }
        sortDeprecatedLists(); 
    } 

    /**
     * Add the members into a single list of deprecated members.
     *
     * @param list List of all the particular deprecated members, e.g. methods.
     * @param members members to be added in the list.
     */
    private void composeDeprecatedList(List list, MemberDoc[] members) { 
        for (int i = 0; i < members.length; i++) {
            if (members[i].tags("deprecated").length > 0) {
                list.add(members[i]);
            }
        }
    }

    /**
     * Sort the deprecated lists for class kinds, fields, methods and
     * constructors.
     */
    private void sortDeprecatedLists() {
        Collections.sort(deprecatedclasses);
        Collections.sort(deprecatedinterfaces);
        Collections.sort(deprecatedexceptions);
        Collections.sort(deprecatederrors);
        Collections.sort(deprecatedfields);
        Collections.sort(deprecatedmethods);
        Collections.sort(deprecatedconstructors);
    }

    /**
     * Return the list of deprecated classes.
     */
    public List getDeprecatedClasses() {
        return deprecatedclasses;
    }

    /**
     * Return the list of deprecated interfaces.
     */
    public List getDeprecatedInterfaces() {
        return deprecatedinterfaces;
    }

    /**
     * Return the list of deprecated errors.
     */
    public List getDeprecatedErrors() {
        return deprecatederrors;
    }

    /**
     * Return the list of deprecated exceptions.
     */
    public List getDeprecatedExceptions() {
        return deprecatedexceptions;
    }

    /**
     * Return the list of deprecated fields.
     */
    public List getDeprecatedFields() {
        return deprecatedfields;
    }

    /**
     * Return the list of deprecated methods.
     */
    public List getDeprecatedMethods() {
        return deprecatedmethods;
    }

    /**
     * Return the list of deprecated constructors.
     */
    public List getDeprecatedConstructors() {
        return deprecatedconstructors;
    }
}
