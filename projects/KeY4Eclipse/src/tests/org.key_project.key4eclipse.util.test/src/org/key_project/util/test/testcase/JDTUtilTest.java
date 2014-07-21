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

package org.key_project.util.test.testcase;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.ILocalVariable;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.Signature;
import org.eclipse.jdt.core.dom.Block;
import org.junit.Test;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.Activator;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link JDTUtil}
 * @author Martin Hentschel
 */
public class JDTUtilTest extends TestCase {
   /**
    * Tests {@link JDTUtil#isInSourceFolder(IResource)}.
    */
   @Test
   public void testIsInSourceFolder() throws CoreException, InterruptedException {
      // Test general Project
      IProject generalProject = TestUtilsUtil.createProject("JDTUtilTest_testIsInSourceFolder_general");
      IFolder generalSrcFolder = TestUtilsUtil.createFolder(generalProject, "src");
      IFile generalJavaFile = TestUtilsUtil.createFile(generalProject, "MyClass.java", "public class MyClass {}");
      IFile generalSoureJavaFile = TestUtilsUtil.createFile(generalSrcFolder, "MyClass.java", "public class MyClass {}");
      IFolder generalPackageFolder = TestUtilsUtil.createFolder(generalSrcFolder, "aPackage");
      IFile generalPackageJavaFile = TestUtilsUtil.createFile(generalPackageFolder, "MyClass.java", "package aPackage;\npublic class MyClass {}");
      assertFalse(JDTUtil.isInSourceFolder(null));
      assertFalse(JDTUtil.isInSourceFolder(generalProject));
      assertFalse(JDTUtil.isInSourceFolder(generalSrcFolder));
      assertFalse(JDTUtil.isInSourceFolder(generalJavaFile));
      assertFalse(JDTUtil.isInSourceFolder(generalSoureJavaFile));
      assertFalse(JDTUtil.isInSourceFolder(generalPackageFolder));
      assertFalse(JDTUtil.isInSourceFolder(generalPackageJavaFile));
      // Test Java Project
      IJavaProject javaProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testIsInSourceFolder_java");
      IFolder javaProjectSrcFolder = javaProject.getProject().getFolder("src");
      IFile javaJavaFile = TestUtilsUtil.createFile(javaProject.getProject(), "MyClass.java", "public class MyClass {}");
      IFile javaSoureJavaFile = TestUtilsUtil.createFile(javaProjectSrcFolder, "MyClass.java", "public class MyClass {}");
      IFolder javaPackageFolder = TestUtilsUtil.createFolder(javaProjectSrcFolder, "aPackage");
      IFile javaPackageJavaFile = TestUtilsUtil.createFile(javaPackageFolder, "MyClass.java", "package aPackage;\npublic class MyClass {}");
      assertFalse(JDTUtil.isInSourceFolder(null));
      assertFalse(JDTUtil.isInSourceFolder(javaProject.getProject()));
      assertTrue(JDTUtil.isInSourceFolder(javaProjectSrcFolder));
      assertFalse(JDTUtil.isInSourceFolder(javaJavaFile));
      assertTrue(JDTUtil.isInSourceFolder(javaSoureJavaFile));
      assertTrue(JDTUtil.isInSourceFolder(javaPackageFolder));
      assertTrue(JDTUtil.isInSourceFolder(javaPackageJavaFile));
      // Test Java Project (no bin/src folders)
      IJavaProject noBinSrcJavaProject = TestUtilsUtil.createJavaProjectNoBinSourceFolders("JDTUtilTest_testIsInSourceFolder_javaNoBinSrc");
      IFile noBinSrcJavaJavaFile = TestUtilsUtil.createFile(noBinSrcJavaProject.getProject(), "MyClass.java", "public class MyClass {}");
      IFolder noBinSrcJavaPackageFolder = TestUtilsUtil.createFolder(noBinSrcJavaProject.getProject(), "aPackage");
      IFile noBinSrcJavaPackageJavaFile = TestUtilsUtil.createFile(noBinSrcJavaPackageFolder, "MyClass.java", "package aPackage;\npublic class MyClass {}");
      assertFalse(JDTUtil.isInSourceFolder(null));
      assertTrue(JDTUtil.isInSourceFolder(noBinSrcJavaProject.getProject()));
      assertTrue(JDTUtil.isInSourceFolder(noBinSrcJavaJavaFile));
      assertTrue(JDTUtil.isInSourceFolder(noBinSrcJavaPackageFolder));
      assertTrue(JDTUtil.isInSourceFolder(noBinSrcJavaPackageJavaFile));
   }
   
   /**
    * Tests {@link JDTUtil#isJavaFile(org.eclipse.core.resources.IFile)}.
    */
   @Test
   public void testIsJavaFile() throws CoreException {
      IProject project = TestUtilsUtil.createProject("JDTUtilTest_testIsJavaFile");
      IFile file = TestUtilsUtil.createFile(project, "noExtension", "noExtension");
      IFile txtFile = TestUtilsUtil.createFile(project, "txtFile.txt", "txtFile");
      IFile javaFile = TestUtilsUtil.createFile(project, "javaFile.java", "javaFile");
      IFile javaDifferentCasesFile = TestUtilsUtil.createFile(project, "javaDifferentCasesFile.jAVa", "javaDifferentCasesFile");
      assertFalse(JDTUtil.isJavaFile(null));
      assertFalse(JDTUtil.isJavaFile(file));
      assertFalse(JDTUtil.isJavaFile(txtFile));
      assertTrue(JDTUtil.isJavaFile(javaFile));
      assertTrue(JDTUtil.isJavaFile(javaDifferentCasesFile));
   }

   /**
    * Tests {@link JDTUtil#getTabWidth(IJavaElement)}.
    */
   @Test
   public void testGetTabWidth() throws CoreException, InterruptedException {
      // Create test project and content
      IJavaProject project = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetTabWidth");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MethodTest", src);
      TestUtilsUtil.waitForBuild();
      IMethod method = TestUtilsUtil.getJdtMethod(project, "MethodTest", "voidMethod");
      // Get tab width
      assertEquals(0, JDTUtil.getTabWidth(null));
      assertEquals(4, JDTUtil.getTabWidth(method));
   }
   
   /**
    * Tests {@link JDTUtil#getMethodBody(IMethod)}.
    */
   @Test
   public void testGetMethodBody() throws CoreException, InterruptedException {
      // Create projects with test content
      IJavaProject javaProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetMethodBody");
      IFolder srcFolder = javaProject.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/methodBodyTest", srcFolder);
      TestUtilsUtil.waitForBuild();
      // Get type
      IType type = javaProject.findType("MethodBodyTest");
      // Test null
      assertNull(JDTUtil.getMethodBody(null));
      // Test methods
      assertMethodBody(type, "emptyVoid", new String[] {}, "{ }");
      assertMethodBody(type, "emptyVoidSingleLined", new String[] {}, "{ }");
      assertMethodBody(type, "doSomething", new String[] {}, "{ int x=32; }");
      assertMethodBody(type, "returnInt", new String[] {}, "{ return 42; }");
      assertMethodBody(type, "containsIf", new String[] {"I"}, "{ if (x >= 0) { return x; } else return x * -1; }");
   }
   
   /**
    * Executes a test step of {@link #testGetMethodBody()}.
    * @param type The {@link IType} to search a method in.
    * @param name The method name.
    * @param parameterTypeSignatures The method parameter types.
    * @param expectedBlock The expected block.
    * @throws JavaModelException Occurred Exception.
    */
   protected void assertMethodBody(IType type, 
                                   String name, 
                                   String[] parameterTypeSignatures, 
                                   String expectedBlock) throws JavaModelException {
      IMethod method = type.getMethod(name, parameterTypeSignatures);
      assertNotNull(method);
      Block block = JDTUtil.getMethodBody(method);
      assertNotNull(block);
      assertTrue("Expected \"" + expectedBlock + "\" but is \"" + block.toString() + "\".", StringUtil.equalIgnoreWhiteSpace(expectedBlock, block.toString()));
      assertTrue(block.getStartPosition() >= method.getSourceRange().getOffset());
      assertTrue(block.getStartPosition() + block.getLength() <= method.getSourceRange().getOffset() + method.getSourceRange().getLength());
   }
   
    /**
     * Tests {@link JDTUtil#getQualifiedParameterType(IType, org.eclipse.jdt.core.ILocalVariable)}.
     */
    @Test
    public void testGetQualifiedParameterType() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetQualifiedParameterType");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/SignatureLabelTest", srcFolder);
        // Get type
        IType type = javaProject.findType("SignatureLabelTest");
        assertNotNull(type);
        IMethod[] methods = type.getMethods();
        IMethod method = JDTUtil.getElementForQualifiedMethodLabel(methods, "ADateBDate(a.Date, b.Date)");
        assertNotNull(method);
        ILocalVariable[] parameters = method.getParameters();
        assertEquals(2, parameters.length);
        // Test null type
        assertNull(JDTUtil.getQualifiedParameterType(null, parameters[0]));
        // Test null parameter
        assertNull(JDTUtil.getQualifiedParameterType(type, null));
        // Test both null
        assertNull(JDTUtil.getQualifiedParameterType(null, null));
        // Test methods parameter
        assertEquals("a.Date", JDTUtil.getQualifiedParameterType(type, parameters[0]));
        assertEquals("b.Date", JDTUtil.getQualifiedParameterType(type, parameters[1]));
    }
    
    /**
     * Tests {@link JDTUtil#getElementForQualifiedMethodLabel(IMethod[], String)}
     * @throws InterruptedException 
     * @throws CoreException 
     */
    @Test
    public void testGetElementForQualifiedMethodLabel() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetElementForQualifiedMethodLabel");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MethodTest", srcFolder);
        // Get type
        IType type = javaProject.findType("MethodTest");
        assertNotNull(type);
        IMethod[] methods = type.getMethods();
        assertTrue(methods != null && methods.length >= 1);
        // Test null text label
        assertEquals(null, JDTUtil.getElementForQualifiedMethodLabel(methods, null));
        // Test null elements
        assertEquals(null, JDTUtil.getElementForQualifiedMethodLabel(null, JDTUtil.getQualifiedMethodLabel(methods[0])));
        // Test invalid label
        assertEquals(null, JDTUtil.getElementForQualifiedMethodLabel(methods, "invalid()"));
        // Test valid methods
        for (IMethod method : methods) {
            assertSame(method, JDTUtil.getElementForQualifiedMethodLabel(methods, JDTUtil.getQualifiedMethodLabel(method)));
        }
    }
    
    /**
     * Tests {@link JDTUtil#getQualifiedMethodLabel(IMethod)}.
     */
    @Test
    public void testGetQualifiedMethodLabel() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetQualifiedMethodLabel");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/SignatureLabelTest", srcFolder);
        // Get type
        IType type = javaProject.findType("SignatureLabelTest");
        IMethod[] methods = type.getMethods();
        String[] expectedLabels = new String[] { "booleanParam(boolean)",
                                                 "byteParam(byte)",
                                                 "shortParam(short)",
                                                 "intParam(int)",
                                                 "longParam(long)",
                                                 "doubleParam(double)",
                                                 "floatParam(float)",
                                                 "charParam(char)",
                                                 "objectParam(java.lang.Object)",
                                                 "stringParam(java.lang.String)",
                                                 "booleanArrayParam(boolean[])",
                                                 "byteArrayParam(byte[])",
                                                 "shortArrayParam(short[])",
                                                 "intArrayParam(int[])",
                                                 "longArrayParam(long[])",
                                                 "doubleArrayParam(double[])",
                                                 "floatArrayParam(float[])",
                                                 "charArrayParam(char[])",
                                                 "objectArrayParam(java.lang.Object[])",
                                                 "stringArrayParam(java.lang.String[])",
                                                 "booleanArrayArrayParam(boolean[][])",
                                                 "byteArrayArrayParam(byte[][])",
                                                 "shortArrayArrayParam(short[][])",
                                                 "intArrayArrayParam(int[][])",
                                                 "longArrayArrayParam(long[][])",
                                                 "doubleArrayArrayParam(double[][])",
                                                 "floatArrayArrayParam(float[][])",
                                                 "charArrayArrayParam(char[][])",
                                                 "objectArrayArrayParam(java.lang.Object[][])",
                                                 "stringArrayArrayParam(java.lang.String[][])",
                                                 "ADateADate(a.Date, a.Date)",
                                                 "ADateBDate(a.Date, b.Date)",
                                                 "BDateBDate(b.Date, b.Date)"
        };
        for (int i = 0; i < methods.length; i++) {
            String label = JDTUtil.getQualifiedMethodLabel(methods[i]);
            assertEquals(expectedLabels[i], label);
        }
    }
    
    /**
     * Tests {@link JDTUtil#getElementForTextLabel(IJavaElement[], String)}
     * @throws InterruptedException 
     * @throws CoreException 
     */
    @Test
    public void testGetElementForTextLabel() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetElementForTextLabel");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MethodTest", srcFolder);
        // Get type
        IType type = javaProject.findType("MethodTest");
        assertNotNull(type);
        IMethod[] methods = type.getMethods();
        assertTrue(methods != null && methods.length >= 1);
        // Test null text label
        assertEquals(null, JDTUtil.getElementForTextLabel(methods, null));
        // Test null elements
        assertEquals(null, JDTUtil.getElementForTextLabel(null, JDTUtil.getTextLabel(methods[0])));
        // Test invalid label
        assertEquals(null, JDTUtil.getElementForTextLabel(methods, "invalid()"));
        // Test valid methods
        for (IMethod method : methods) {
            assertSame(method, JDTUtil.getElementForTextLabel(methods, JDTUtil.getTextLabel(method)));
        }
    }
    
    /**
     * Tests {@link JDTUtil#getTextLabel(IJavaElement)}
     */
    @Test
    public void testGetTextLabel() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetTextLabel");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        IFolder banking = TestUtilsUtil.createFolder(srcFolder, "banking");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        // Get method
        IMethod method = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        // Test null
        assertEquals(StringUtil.EMPTY_STRING, JDTUtil.getTextLabel(null));
        // Test method
        assertEquals("charge(int)", JDTUtil.getTextLabel(method));
    }
    
    /**
     * Tests {@link JDTUtil#addClasspathEntry(IJavaProject, org.eclipse.jdt.core.IClasspathEntry)}
     */
    @Test
    public void testAddClasspathEntry() throws CoreException, InterruptedException {
        // Create initial java project
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testAddClasspathEntry");
        IFolder src = javaProject.getProject().getFolder("src");
        IClasspathEntry[] defaultEntries = TestUtilsUtil.getDefaultJRELibrary();
        IClasspathEntry[] entries = javaProject.getRawClasspath();
        assertEquals(1 + defaultEntries.length, entries.length);
        assertEquals(src.getFullPath(), entries[0].getPath());
        for (int i = 1; i < entries.length; i++) {
            assertEquals(entries[i], defaultEntries[i - 1]);
        }
        // Test null execution which should do nothing
        IFolder secondSrc = javaProject.getProject().getFolder("secondSrc");
        if (!secondSrc.exists()) {
            secondSrc.create(true, true, null);
        }
        JDTUtil.addClasspathEntry(null, null);
        JDTUtil.addClasspathEntry(null, JavaCore.newSourceEntry(secondSrc.getFullPath()));
        JDTUtil.addClasspathEntry(javaProject, null);
        entries = javaProject.getRawClasspath();
        assertEquals(1 + defaultEntries.length, entries.length);
        assertEquals(src.getFullPath(), entries[0].getPath());
        for (int i = 1; i < entries.length; i++) {
            assertEquals(entries[i], defaultEntries[i - 1]);
        }
        // Add path entry
        JDTUtil.addClasspathEntry(javaProject, JavaCore.newSourceEntry(secondSrc.getFullPath()));
        entries = javaProject.getRawClasspath();
        assertEquals(2 + defaultEntries.length, entries.length);
        assertEquals(src.getFullPath(), entries[0].getPath());
        for (int i = 1; i < defaultEntries.length; i++) {
            assertEquals(entries[i], defaultEntries[i - 1]);
        }
        assertEquals(secondSrc.getFullPath(), entries[entries.length - 1].getPath());
    }
    
    /**
     * Tests {@link JDTUtil#getSourceLocations(IProject)}
     */
    @Test
    public void testGetSourceLocations() throws CoreException, InterruptedException {
        // Test null
        List<File> locations = JDTUtil.getSourceLocations(null);
        assertNotNull(locations);
        assertEquals(0, locations.size());
        // Test general project
        IProject project = TestUtilsUtil.createProject("JDTUtilTest_testGetSourceLocations_general");
        locations = JDTUtil.getSourceLocations(project);
        assertNotNull(locations);
        assertEquals(0, locations.size());
        // Test Java project with one source location in project
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetSourceLocations_Java");
        project = javaProject.getProject();
        IFolder src = project.getFolder("src");
        assertNotNull(src);
        assertTrue(src.exists());
        locations = JDTUtil.getSourceLocations(project);
        assertNotNull(locations);
        assertEquals(1, locations.size());
        assertEquals(ResourceUtil.getLocation(src), locations.get(0));
        // Add second source location in project
        IFolder secondSrc = project.getFolder("secondSrc");
        if (!secondSrc.exists()) {
            secondSrc.create(true, true, null);
        }
        JDTUtil.addClasspathEntry(javaProject, JavaCore.newSourceEntry(secondSrc.getFullPath()));
        // Test Java project with two source location in project
        locations = JDTUtil.getSourceLocations(project);
        assertNotNull(locations);
        assertEquals(2, locations.size());
        assertEquals(ResourceUtil.getLocation(src), locations.get(0));
        assertEquals(ResourceUtil.getLocation(secondSrc), locations.get(1));
        // Add class path entry for a different java project
        IJavaProject refJavaProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetSourceLocations_Java_Refereneed");
        IProject refProject = refJavaProject.getProject();
        IFolder refSrc = refProject.getFolder("src");
        assertNotNull(refSrc);
        assertTrue(refSrc.exists());
        JDTUtil.addClasspathEntry(javaProject, JavaCore.newSourceEntry(refJavaProject.getPath()));
        // Test Java project with two source location in project and project reference
        locations = JDTUtil.getSourceLocations(project);
        assertNotNull(locations);
        assertEquals(3, locations.size());
        assertEquals(ResourceUtil.getLocation(src), locations.get(0));
        assertEquals(ResourceUtil.getLocation(secondSrc), locations.get(1));
        assertEquals(ResourceUtil.getLocation(refSrc), locations.get(2));
        locations = JDTUtil.getSourceLocations(refProject);
        assertNotNull(locations);
        assertEquals(1, locations.size());
        assertEquals(ResourceUtil.getLocation(refSrc), locations.get(0));
        // Create cycle by also referencing javaProject in refJavaProject
        JDTUtil.addClasspathEntry(refJavaProject, JavaCore.newSourceEntry(javaProject.getPath()));
        // Test Java project with two source location in project and cyclic project reference
        locations = JDTUtil.getSourceLocations(project);
        assertNotNull(locations);
        assertEquals(3, locations.size());
        assertEquals(ResourceUtil.getLocation(src), locations.get(0));
        assertEquals(ResourceUtil.getLocation(secondSrc), locations.get(1));
        assertEquals(ResourceUtil.getLocation(refSrc), locations.get(2));
        locations = JDTUtil.getSourceLocations(refProject);
        assertNotNull(locations);
        assertEquals(3, locations.size());
        assertEquals(ResourceUtil.getLocation(refSrc), locations.get(0));
        assertEquals(ResourceUtil.getLocation(src), locations.get(1));
        assertEquals(ResourceUtil.getLocation(secondSrc), locations.get(2));
    }
    
    /**
     * Tests {@link JDTUtil#isJavaProject(IProject)}
     */
    @Test
    public void testIsJavaProject() throws CoreException, InterruptedException {
        // Test null
        assertFalse(JDTUtil.isJavaProject(null));
        // Test general project
        IProject project = TestUtilsUtil.createProject("JDTUtilTest_testisJavaProject_general");
        assertFalse(JDTUtil.isJavaProject(project));
        // Test Java project
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testisJavaProject_Java"); 
        assertTrue(JDTUtil.isJavaProject(javaProject.getProject()));
    }

    /**
     * Tests {@link JDTUtil#getJavaProject(String)}
     */
    @Test
    public void testGetJavaProject_String() throws CoreException, InterruptedException {
        // Test null
        assertNull(JDTUtil.getJavaProject((String)null));
        // Test general project
        IProject project = TestUtilsUtil.createProject("JDTUtilTest_testGetJavaProject_String_general");
        IJavaProject javaProject = JDTUtil.getJavaProject(project.getName());
        assertNull(JDTUtil.getJavaProject((String)null));
        assertEquals(project, javaProject.getProject());
        // Test Java project
        IJavaProject createdProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetJavaProject_String_Java"); 
        project = createdProject.getProject();
        javaProject = JDTUtil.getJavaProject(project.getName());
        assertNull(JDTUtil.getJavaProject((String)null));
        assertEquals(project, javaProject.getProject());
        assertEquals(createdProject, javaProject);
    }

    /**
     * Tests {@link JDTUtil#getJavaProject(IProject)}
     */
    @Test
    public void testGetJavaProject_IProject() throws CoreException, InterruptedException {
        // Test null
        assertNull(JDTUtil.getJavaProject((IProject)null));
        // Test general project
        IProject project = TestUtilsUtil.createProject("JDTUtilTest_testGetJavaProject_IProject_general");
        IJavaProject javaProject = JDTUtil.getJavaProject(project);
        assertNull(JDTUtil.getJavaProject((IProject)null));
        assertEquals(project, javaProject.getProject());
        // Test Java project
        IJavaProject createdProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetJavaProject_IProject_Java"); 
        project = createdProject.getProject();
        javaProject = JDTUtil.getJavaProject(project);
        assertNull(JDTUtil.getJavaProject((IProject)null));
        assertEquals(project, javaProject.getProject());
        assertEquals(createdProject, javaProject);
    }
    
    /**
     * Tests {@link JDTUtil#getPackage(IJavaElement)}
     */
    @Test
    public void testGetPackage() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject jdt = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetPackage");
        IFolder srcFolder = jdt.getProject().getFolder("src");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/getPackage", srcFolder);
        // Get java project
        IJavaElement projectTest = JDTUtil.getPackage(jdt);
        assertNull(projectTest);
        // Get java model
        IJavaElement modelTest = JDTUtil.getPackage(jdt.getJavaModel());
        assertNull(modelTest);
        // Get packageA
        IJavaElement packageA = jdt.findElement(new Path("packageA"));
        IJavaElement packageATest = JDTUtil.getPackage(packageA);
        assertEquals(packageA, packageATest);
        // Get packageA.ClassA
        IType classA = jdt.findType("packageA.ClassA");
        IJavaElement classATest = JDTUtil.getPackage(classA);
        assertEquals(packageA, classATest);
        // Get packageB
        IJavaElement packageB = jdt.findElement(new Path("packageB"));
        IJavaElement packageBTest = JDTUtil.getPackage(packageB);
        assertEquals(packageB, packageBTest);
        // Get packageB.C
        IJavaElement packageC = jdt.findElement(new Path("packageB/C"));
        IJavaElement packageCTest = JDTUtil.getPackage(packageC);
        assertEquals(packageC, packageCTest);
        // Get packageB.C.D
        IJavaElement packageD = jdt.findElement(new Path("packageB/C/D"));
        IJavaElement packageDTest = JDTUtil.getPackage(packageD);
        assertEquals(packageD, packageDTest);
        // Get packageB.C.D.ClassB
        IType classB = jdt.findType("packageB.C.D.ClassB");
        IJavaElement classBTest = JDTUtil.getPackage(classB);
        assertEquals(packageD, classBTest);
        // Get <default>
        IPackageFragment defaultPackage = jdt.findPackageFragment(srcFolder.getFullPath());
        IJavaElement defaultPackageTest = JDTUtil.getPackage(defaultPackage);
        assertEquals(defaultPackage, defaultPackageTest);
        // Get ClassRoot
        IType classRoot = jdt.findType("ClassRoot");
        IJavaElement classRootTest = JDTUtil.getPackage(classRoot);
        assertEquals(defaultPackage, classRootTest);
    }
    
    /**
     * Tests {@link JDTUtil#getAllPackageFragmentRoot()}
     */
    @Test
    public void testGetAllPackageFragmentRoot() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject jdt1 = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetAllPackageFragmentRoot1");
        IJavaProject jdt2 = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetAllPackageFragmentRoot2");
        IFolder srcFolder1 = jdt1.getProject().getFolder("src");
        IFolder srcFolder2 = jdt2.getProject().getFolder("src");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/packagesRoots1", srcFolder1);
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/packagesRoots2", srcFolder2);
        // Get expected folders
        IFolder packageA = srcFolder1.getFolder("packageA");
        IFolder packageB = srcFolder2.getFolder("packageB");
        IFolder b1 = packageB.getFolder("B1");
        IFolder b2 = packageB.getFolder("B2");
        IFolder b23 = b2.getFolder("B3");
        IFolder b234 = b23.getFolder("B4");
        List<IResource> expectedResources = new LinkedList<IResource>();
        expectedResources.add(packageA);
        expectedResources.add(packageB);
        expectedResources.add(b1);
        expectedResources.add(b2);
        expectedResources.add(b23);
        expectedResources.add(b234);
        // List package roots
        IJavaElement[] roots = JDTUtil.getAllPackageFragmentRoot();
        // Make sure that the test packages are contained
        for (IJavaElement root : roots) {
           expectedResources.remove(root.getResource());
        }
        assertEquals(0, expectedResources.size());
    }
    
    /**
     * Tests {@link JDTUtil#getAllJavaProjects()}
     */
    @Test
    public void testGetAllJavaProjects() throws CoreException, InterruptedException {
        // Create projects
        IProject general1 = TestUtilsUtil.createProject("JDTUtilTest_testGetAllJavaProjects1");
        IJavaProject jdt1 = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetAllJavaProjects2");
        IProject general2 = TestUtilsUtil.createProject("JDTUtilTest_testGetAllJavaProjects3");
        IJavaProject jdt2 = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetAllJavaProjects4");
        // List all java projects
        IJavaProject[] allJavaProjects = JDTUtil.getAllJavaProjects();
        assertNotNull(allJavaProjects);
        assertTrue(allJavaProjects.length >= 2);
        boolean general1Found = false;
        boolean general2Found = false;
        boolean jdt1Found = false;
        boolean jdt2Found = false;
        for (IJavaProject jProejct : allJavaProjects) {
           if (jProejct.getProject().equals(general1)) {
              general1Found = true;
           }
           else if (jProejct.getProject().equals(general2)) {
              general2Found = true;
           }
           else if (jProejct.getProject().equals(jdt1.getProject())) {
              jdt1Found = true;
           }
           else if (jProejct.getProject().equals(jdt2.getProject())) {
              jdt2Found = true;
           }
        }
        assertFalse(general1Found);
        assertFalse(general2Found);
        assertTrue(jdt1Found);
        assertTrue(jdt2Found);
    }
}