/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.ui.test.testcase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.search.IJavaSearchScope;
import org.eclipse.jdt.core.search.SearchEngine;
import org.key_project.sed.key.ui.jdt.AllOperationsSearchEngine;
import org.key_project.sed.key.ui.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link AllOperationsSearchEngine}.
 * @author Martin Hentschel
 */
public class AllOperationsSearchEngineTest extends AbstractSetupTestCase {
    /**
     * Executes a search in that inner and anonymous types are included.
     */
    public void testSearchResult_noInnerAnonymousTypes_noAnnotations() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("AllOperationsSearchEngineTest_testSearchResult_noInnerAnonymousTypes_noAnnotations");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/typesAndMethods", srcFolder);
        javaProject.open(null);
        assertTrue(javaProject.isOpen());
        // Execute search
        IJavaSearchScope searchScope = SearchEngine.createJavaSearchScope(new IJavaElement[] {javaProject}, IJavaSearchScope.SOURCES);
        AllOperationsSearchEngine engine = new AllOperationsSearchEngine();
        IMethod[] methods = engine.searchOperations(new NullProgressMonitor(), searchScope);
        doCompareTestResult(methods, 
                            "InMainPackage.methodInMainPackage()",
                            "InAPackage.methodInAPackage()",
                            "AnonymousTypesParent.doSomething()",
                            "InBbBPackage.methodInBbBPackage()",
                            "MethodsWithSignatures.MethodsWithSignatures()",
                            "MethodsWithSignatures.MethodsWithSignatures(int)",
                            "MethodsWithSignatures.MethodsWithSignatures(int, java.lang.String)",
                            "MethodsWithSignatures.voidMethod()",
                            "MethodsWithSignatures.stringMethod()",
                            "MethodsWithSignatures.intMethod()",
                            "MethodsWithSignatures.intArrayMethod()",
                            "MethodsWithSignatures.intParam(int)",
                            "MethodsWithSignatures.stringParam(java.lang.String)",
                            "MethodsWithSignatures.intStringParam(int, java.lang.String)",
                            "MethodsWithSignatures.intArrayParam(int[])",
                            "MethodsWithSignatures.overloading()",
                            "MethodsWithSignatures.overloading(int)",
                            "MethodsWithSignatures.overloading(java.lang.String)",
                            "MethodsWithSignatures.overloading(java.lang.String, int)",
                            "MethodsWithSignatures.utilDateUtilDate(java.util.Date, java.util.Date)",
                            "MethodsWithSignatures.utilDateSqlDate(java.util.Date, java.sql.Date)",
                            "MethodsWithSignatures.sqlDateSqlDate(java.sql.Date, java.sql.Date)",
                            "AClass.methodInAClass()",
                            "AEnum.methodInAEnum()",
                            "AInterface.methodInAInterface()");
    }
    
    /**
     * Executes a search in that inner and anonymous types are included.
     */
    public void testSearchResult_noInnerAnonymousTypes_withAnnotations() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("AllOperationsSearchEngineTest_testSearchResult_noInnerAnonymousTypes_withAnnotations");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/typesAndMethods", srcFolder);
        javaProject.open(null);
        assertTrue(javaProject.isOpen());
        // Execute search
        IJavaSearchScope searchScope = SearchEngine.createJavaSearchScope(new IJavaElement[] {javaProject}, IJavaSearchScope.SOURCES);
        AllOperationsSearchEngine engine = new AllOperationsSearchEngine();
        engine.setIncludeOperationsOfAnnotations(true);
        IMethod[] methods = engine.searchOperations(new NullProgressMonitor(), searchScope);
        doCompareTestResult(methods, 
                            "InMainPackage.methodInMainPackage()",
                            "InAPackage.methodInAPackage()",
                            "AnonymousTypesParent.doSomething()",
                            "InBbBPackage.methodInBbBPackage()",
                            "MethodsWithSignatures.MethodsWithSignatures()",
                            "MethodsWithSignatures.MethodsWithSignatures(int)",
                            "MethodsWithSignatures.MethodsWithSignatures(int, java.lang.String)",
                            "MethodsWithSignatures.voidMethod()",
                            "MethodsWithSignatures.stringMethod()",
                            "MethodsWithSignatures.intMethod()",
                            "MethodsWithSignatures.intArrayMethod()",
                            "MethodsWithSignatures.intParam(int)",
                            "MethodsWithSignatures.stringParam(java.lang.String)",
                            "MethodsWithSignatures.intStringParam(int, java.lang.String)",
                            "MethodsWithSignatures.intArrayParam(int[])",
                            "MethodsWithSignatures.overloading()",
                            "MethodsWithSignatures.overloading(int)",
                            "MethodsWithSignatures.overloading(java.lang.String)",
                            "MethodsWithSignatures.overloading(java.lang.String, int)",
                            "MethodsWithSignatures.utilDateUtilDate(java.util.Date, java.util.Date)",
                            "MethodsWithSignatures.utilDateSqlDate(java.util.Date, java.sql.Date)",
                            "MethodsWithSignatures.sqlDateSqlDate(java.sql.Date, java.sql.Date)",
                            "AAnnotation.methodInAAnnotation()",
                            "AClass.methodInAClass()",
                            "AEnum.methodInAEnum()",
                            "AInterface.methodInAInterface()");
    }
    
    /**
     * Executes a search in that inner and anonymous types are included.
     */
    public void testSearchResult_withInnerAnonymousTypes_noAnnotations() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("AllOperationsSearchEngineTest_testSearchResult_withInnerAnonymousTypes_noAnnotations");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/typesAndMethods", srcFolder);
        javaProject.open(null);
        assertTrue(javaProject.isOpen());
        // Execute search
        IJavaSearchScope searchScope = SearchEngine.createJavaSearchScope(new IJavaElement[] {javaProject}, IJavaSearchScope.SOURCES);
        AllOperationsSearchEngine engine = new AllOperationsSearchEngine();
        engine.setIncludeOperationsOfInnerAndAnonymousTypes(true);
        IMethod[] methods = engine.searchOperations(new NullProgressMonitor(), searchScope);
        doCompareTestResult(methods, 
                            "InMainPackage.methodInMainPackage()",
                            "InAPackage.methodInAPackage()",
                            "AnonymousTypesParent.doSomething()",
                            "new AInterface() {...}.methodInAInterface()",
                            "new AAnnotation() {...}.annotationType()",
                            "new AAnnotation() {...}.methodInAAnnotation()",
                            "InBbBPackage.methodInBbBPackage()",
                            "InnerEnum.methodInInnerEnum()",
                            "InnerInnerEnum.methodInInnerInnerEnum()",
                            "InnerInterface.methodInInnterInterface()",
                            "InnerInnerInterface.methodInInnerInnerInterface()",
                            "InnerClass.methodInInnerClass()",
                            "InnerInnerClss.methodInInnerInnerClass()",
                            "MethodsWithSignatures.MethodsWithSignatures()",
                            "MethodsWithSignatures.MethodsWithSignatures(int)",
                            "MethodsWithSignatures.MethodsWithSignatures(int, java.lang.String)",
                            "MethodsWithSignatures.voidMethod()",
                            "MethodsWithSignatures.stringMethod()",
                            "MethodsWithSignatures.intMethod()",
                            "MethodsWithSignatures.intArrayMethod()",
                            "MethodsWithSignatures.intParam(int)",
                            "MethodsWithSignatures.stringParam(java.lang.String)",
                            "MethodsWithSignatures.intStringParam(int, java.lang.String)",
                            "MethodsWithSignatures.intArrayParam(int[])",
                            "MethodsWithSignatures.overloading()",
                            "MethodsWithSignatures.overloading(int)",
                            "MethodsWithSignatures.overloading(java.lang.String)",
                            "MethodsWithSignatures.overloading(java.lang.String, int)",
                            "MethodsWithSignatures.utilDateUtilDate(java.util.Date, java.util.Date)",
                            "MethodsWithSignatures.utilDateSqlDate(java.util.Date, java.sql.Date)",
                            "MethodsWithSignatures.sqlDateSqlDate(java.sql.Date, java.sql.Date)",
                            "AClass.methodInAClass()",
                            "AEnum.methodInAEnum()",
                            "AInterface.methodInAInterface()");
    }
    
    /**
     * Executes a search in that inner and anonymous types are included.
     */
    public void testSearchResult_withInnerAnonymousTypes_withAnnotations() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("AllOperationsSearchEngineTest_testSearchResult_withInnerAnonymousTypes_withAnnotations");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/typesAndMethods", srcFolder);
        javaProject.open(null);
        assertTrue(javaProject.isOpen());
        // Execute search
        IJavaSearchScope searchScope = SearchEngine.createJavaSearchScope(new IJavaElement[] {javaProject}, IJavaSearchScope.SOURCES);
        AllOperationsSearchEngine engine = new AllOperationsSearchEngine();
        engine.setIncludeOperationsOfAnnotations(true);
        engine.setIncludeOperationsOfInnerAndAnonymousTypes(true);
        IMethod[] methods = engine.searchOperations(new NullProgressMonitor(), searchScope);
        doCompareTestResult(methods, 
                            "InMainPackage.methodInMainPackage()",
                            "InAPackage.methodInAPackage()",
                            "AnonymousTypesParent.doSomething()",
                            "new AInterface() {...}.methodInAInterface()",
                            "new AAnnotation() {...}.annotationType()",
                            "new AAnnotation() {...}.methodInAAnnotation()",
                            "InBbBPackage.methodInBbBPackage()",
                            "InnerAnnotation.methodInInnerAnnotation()",
                            "InnerInnerAnnotation.methodInInnerInnerAnnotation()",
                            "InnerEnum.methodInInnerEnum()",
                            "InnerInnerEnum.methodInInnerInnerEnum()",
                            "InnerInterface.methodInInnterInterface()",
                            "InnerInnerInterface.methodInInnerInnerInterface()",
                            "InnerClass.methodInInnerClass()",
                            "InnerInnerClss.methodInInnerInnerClass()",
                            "MethodsWithSignatures.MethodsWithSignatures()",
                            "MethodsWithSignatures.MethodsWithSignatures(int)",
                            "MethodsWithSignatures.MethodsWithSignatures(int, java.lang.String)",
                            "MethodsWithSignatures.voidMethod()",
                            "MethodsWithSignatures.stringMethod()",
                            "MethodsWithSignatures.intMethod()",
                            "MethodsWithSignatures.intArrayMethod()",
                            "MethodsWithSignatures.intParam(int)",
                            "MethodsWithSignatures.stringParam(java.lang.String)",
                            "MethodsWithSignatures.intStringParam(int, java.lang.String)",
                            "MethodsWithSignatures.intArrayParam(int[])",
                            "MethodsWithSignatures.overloading()",
                            "MethodsWithSignatures.overloading(int)",
                            "MethodsWithSignatures.overloading(java.lang.String)",
                            "MethodsWithSignatures.overloading(java.lang.String, int)",
                            "MethodsWithSignatures.utilDateUtilDate(java.util.Date, java.util.Date)",
                            "MethodsWithSignatures.utilDateSqlDate(java.util.Date, java.sql.Date)",
                            "MethodsWithSignatures.sqlDateSqlDate(java.sql.Date, java.sql.Date)",
                            "AAnnotation.methodInAAnnotation()",
                            "AClass.methodInAClass()",
                            "AEnum.methodInAEnum()",
                            "AInterface.methodInAInterface()");
    }
    
    /**
     * Compares the found methods with the expected one.
     * @param result The found {@link IMethod}.
     * @param expectedSignatures The expected signatures.
     * @throws JavaModelException Occurred Exception.
     */
    public void doCompareTestResult(IMethod[] result, String... expectedSignatures) throws JavaModelException {
        assertNotNull(result);
        assertEquals(expectedSignatures.length, result.length);
        for (int i = 0; i < result.length; i++) {
            assertEquals(expectedSignatures[i], JDTUtil.getTextLabel(result[i].getParent())+ "." + JDTUtil.getQualifiedMethodLabel(result[i]));
        }
    }
}