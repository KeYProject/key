/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package org.key_project.key4eclipse.util.test.testcase;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.junit.Test;
import org.key_project.key4eclipse.util.eclipse.BundleUtil;
import org.key_project.key4eclipse.util.eclipse.ResourceUtil;
import org.key_project.key4eclipse.util.java.ArrayUtil;
import org.key_project.key4eclipse.util.jdt.JDTUtil;
import org.key_project.key4eclipse.util.test.Activator;
import org.key_project.key4eclipse.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link JDTUtil}
 * @author Martin Hentschel
 */
public class JDTUtilTest extends TestCase {
    /**
     * Tests {@link JDTUtil#getSourceLocations(IProject)}
     */
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
        IClasspathEntry[] newEntries = ArrayUtil.add(javaProject.getRawClasspath(), JavaCore.newSourceEntry(secondSrc.getFullPath()));
        javaProject.setRawClasspath(newEntries, null);
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
        newEntries = ArrayUtil.add(javaProject.getRawClasspath(), JavaCore.newSourceEntry(refJavaProject.getPath()));
        javaProject.setRawClasspath(newEntries, null);
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
        newEntries = ArrayUtil.add(refJavaProject.getRawClasspath(), JavaCore.newSourceEntry(javaProject.getPath()));
        refJavaProject.setRawClasspath(newEntries, null);
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
     * Tests {@link JDTUtil#getJavaProject(IProject)}
     */
    @Test
    public void testGetJavaProject() throws CoreException, InterruptedException {
        // Test null
        assertNull(JDTUtil.getJavaProject(null));
        // Test general project
        IProject project = TestUtilsUtil.createProject("JDTUtilTest_testGetJavaProject_general");
        IJavaProject javaProject = JDTUtil.getJavaProject(project);
        assertNull(JDTUtil.getJavaProject(null));
        assertEquals(project, javaProject.getProject());
        // Test Java project
        IJavaProject createdProject = TestUtilsUtil.createJavaProject("JDTUtilTest_testGetJavaProject_Java"); 
        project = createdProject.getProject();
        javaProject = JDTUtil.getJavaProject(project);
        assertNull(JDTUtil.getJavaProject(null));
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
