package org.key_project.sed.key.ui.test.testcase;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.search.IJavaSearchScope;
import org.eclipse.jdt.core.search.SearchEngine;
import org.key_project.key4eclipse.util.eclipse.BundleUtil;
import org.key_project.key4eclipse.util.jdt.JDTUtil;
import org.key_project.key4eclipse.util.test.util.TestUtilsUtil;
import org.key_project.sed.key.ui.jdt.AllOperationsSearchEngine;
import org.key_project.sed.key.ui.test.Activator;

/**
 * Tests for {@link AllOperationsSearchEngine}.
 * @author Martin Hentschel
 */
public class AllOperationsSearchEngineTest extends TestCase {
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
