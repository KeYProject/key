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

package org.key_project.sed.key.core.test.testcase;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.Launch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.Signature;
import org.junit.Test;
import org.key_project.sed.key.core.test.Activator;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.java.Position;

/**
 * Tests for {@link KeySEDUtil}.
 * @author Martin Hentschel
 */
public class KeySEDUtilTest extends AbstractSetupTestCase {
    /**
     * Tests {@link KeySEDUtil#searchLaunchConfigurations(IMethod, Position, Position)} and
     * {@link KeySEDUtil#searchLaunchConfigurations(org.eclipse.core.resources.IFile)}.
     */
    @Test
    public void testSearchLaunchConfigurations() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeySEDUtilTest_testSearchLaunchConfigurations");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        IFolder banking = TestUtilsUtil.createFolder(srcFolder, "banking");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        // Get method
        IMethod firstMethod = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        IMethod secondMethod = TestUtilsUtil.getJdtMethod(javaProject, "banking.LoggingPayCard", "charge", Signature.C_INT + "");
        // Create first configuration
        ILaunchConfiguration firstConfiguration = KeySEDUtil.createConfiguration(firstMethod, null, null);
        assertNotNull(firstConfiguration);
        ILaunchConfiguration firstConfigurationPart = KeySEDUtil.createConfiguration(firstMethod, new Position(1, 2), new Position(3, 4));
        assertNotNull(firstConfigurationPart);
        // Create second and third configuration
        ILaunchConfiguration secondConfiguration = KeySEDUtil.createConfiguration(secondMethod, null, null);
        assertNotNull(secondConfiguration);
        ILaunchConfiguration secondConfigurationPart = KeySEDUtil.createConfiguration(secondMethod, new Position(5, 6), new Position(7, 8));
        assertNotNull(secondConfigurationPart);
        ILaunchConfiguration thirdConfiguration = KeySEDUtil.createConfiguration(secondMethod, null, null);
        assertNotNull(thirdConfiguration);
        ILaunchConfiguration thirdConfigurationPart = KeySEDUtil.createConfiguration(secondMethod, new Position(5, 6), new Position(7, 8));
        assertNotNull(thirdConfigurationPart);
        ILaunchConfiguration thirdConfigurationPartDifferent = KeySEDUtil.createConfiguration(secondMethod, new Position(9, 10), new Position(11, 12));
        assertNotNull(thirdConfigurationPartDifferent);
        // Create configurations for files
        ILaunchConfiguration firstFileConfiguration = KeySEDUtil.createConfiguration((IFile)firstMethod.getUnderlyingResource(), null);
        assertNotNull(firstFileConfiguration);
        ILaunchConfiguration secondFileConfiguration = KeySEDUtil.createConfiguration((IFile)secondMethod.getUnderlyingResource(), null);
        assertNotNull(secondFileConfiguration);
        ILaunchConfiguration thirdFileConfiguration = KeySEDUtil.createConfiguration((IFile)secondMethod.getUnderlyingResource(), null);
        assertNotNull(thirdFileConfiguration);
        // Test null
        List<ILaunchConfiguration> result = KeySEDUtil.searchLaunchConfigurations(null, null, null);
        assertNotNull(result);
        assertEquals(0, result.size());
        // Search configuration for first method
        result = KeySEDUtil.searchLaunchConfigurations(firstMethod, null, null);
        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals(firstConfiguration, result.get(0));
        // Search configuration for first method with part
        result = KeySEDUtil.searchLaunchConfigurations(firstMethod, new Position(1, 2), new Position(3, 4));
        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals(firstConfigurationPart, result.get(0));
        // Search configurations for second method
        result = KeySEDUtil.searchLaunchConfigurations(secondMethod, null, null);
        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals(secondConfiguration, result.get(0));
        assertEquals(thirdConfiguration, result.get(1));
        // Search configurations for second method with part
        result = KeySEDUtil.searchLaunchConfigurations(secondMethod, new Position(5, 6), new Position(7, 8));
        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals(secondConfigurationPart, result.get(0));
        assertEquals(thirdConfigurationPart, result.get(1));
        // Search configurations for second method with different part
        result = KeySEDUtil.searchLaunchConfigurations(secondMethod, new Position(9, 10), new Position(11, 12));
        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals(thirdConfigurationPartDifferent, result.get(0));
        // Search configurations for second method with not existing part
        result = KeySEDUtil.searchLaunchConfigurations(secondMethod, new Position(9, 10), new Position(42, 42));
        assertNotNull(result);
        assertEquals(0, result.size());
        
        // Test file null
        result = KeySEDUtil.searchLaunchConfigurations(null);
        assertNotNull(result);
        assertEquals(0, result.size());
        // Search configuration for first file
        result = KeySEDUtil.searchLaunchConfigurations((IFile)firstMethod.getUnderlyingResource());
        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals(firstFileConfiguration, result.get(0));
        // Search configuration for second file
        result = KeySEDUtil.searchLaunchConfigurations((IFile)secondMethod.getUnderlyingResource());
        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals(secondFileConfiguration, result.get(0));
        assertEquals(thirdFileConfiguration, result.get(1));
    }
    
    /**
     * Tests {@link KeySEDUtil#createConfiguration(IFile)}.
     */
    @Test
    public void testCreateConfiguration_IFile() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeySEDUtilTest_testCreateConfiguration_IFile");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        IFolder banking = TestUtilsUtil.createFolder(srcFolder, "banking");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        // Get method
        IMethod method = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        // Create configuration without method range and without method
        IFile file = (IFile)method.getUnderlyingResource();
        ILaunchConfiguration configuration = KeySEDUtil.createConfiguration(file, null);
        assertNotNull(configuration);
        assertEquals(file.getFullPath().toString(), KeySEDUtil.getFileToLoadValue(configuration));
        assertFalse(KeySEDUtil.isNewDebugSession(configuration));
        assertNull(KeySEDUtil.findMethod(configuration));
        // Create configuration without method range but with method
        configuration = KeySEDUtil.createConfiguration(file, method);
        assertNotNull(configuration);
        assertEquals(file.getFullPath().toString(), KeySEDUtil.getFileToLoadValue(configuration));
        assertFalse(KeySEDUtil.isNewDebugSession(configuration));
        assertEquals(method, KeySEDUtil.findMethod(configuration));
    }
    
    /**
     * Tests {@link KeySEDUtil#createConfiguration(IMethod, Position, Position)}.
     */
    @Test
    public void testCreateConfiguration_IMethod() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeySEDUtilTest_testCreateConfiguration_IMethod");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        IFolder banking = TestUtilsUtil.createFolder(srcFolder, "banking");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        // Get method
        IMethod method = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        // Create configuration without method range
        ILaunchConfiguration configuration = KeySEDUtil.createConfiguration(method, null, null);
        assertNotNull(configuration);
        assertEquals(javaProject.getProject().getName(), KeySEDUtil.getProjectValue(configuration));
        assertEquals("banking.PayCard", KeySEDUtil.getTypeValue(configuration));
        assertEquals("charge(int)", KeySEDUtil.getMethodValue(configuration));
        assertFalse(KeySEDUtil.isExecuteMethodRange(configuration));
        assertTrue(KeySEDUtil.isNewDebugSession(configuration));
        // Create configuration with method range
        configuration = KeySEDUtil.createConfiguration(method, new Position(1, 2), new Position(3, 4));
        assertNotNull(configuration);
        assertEquals(javaProject.getProject().getName(), KeySEDUtil.getProjectValue(configuration));
        assertEquals("banking.PayCard", KeySEDUtil.getTypeValue(configuration));
        assertEquals("charge(int)", KeySEDUtil.getMethodValue(configuration));
        assertTrue(KeySEDUtil.isExecuteMethodRange(configuration));
        assertEquals(1, KeySEDUtil.getMethodRangeStartLine(configuration));
        assertEquals(2, KeySEDUtil.getMethodRangeStartColumn(configuration));
        assertEquals(3, KeySEDUtil.getMethodRangeEndLine(configuration));
        assertEquals(4, KeySEDUtil.getMethodRangeEndColumn(configuration));
        assertTrue(KeySEDUtil.isNewDebugSession(configuration));
    }
    
    /**
     * Tests {@link KeySEDUtil#getConfigurationType()}.
     */
    @Test
    public void testGetConfigurationType() {
        ILaunchConfigurationType type = KeySEDUtil.getConfigurationType();
        assertNotNull(type);
        assertEquals(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ID, type.getIdentifier());
    }
    
    /**
     * Tests {@link KeySEDUtil#findMethod(org.eclipse.debug.core.ILaunch)}.
     */
    @Test
    public void testFindMethod_ILaunch() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeySEDUtilTest_testFindMethod_ILaunch");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        IFolder banking = TestUtilsUtil.createFolder(srcFolder, "banking");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        // Get method
        IMethod method = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        // Create configuration
        ILaunchConfiguration configuration = KeySEDUtil.createConfiguration(method, null, null);
        assertNotNull(configuration);
        // Create launch
        ILaunch launch = new Launch(configuration, KeySEDUtil.MODE, null);
        // Test null
        assertNull(KeySEDUtil.findMethod((ILaunch)null));
        // Test method
        assertEquals(method, KeySEDUtil.findMethod(launch));
    }

    /**
     * Tests {@link KeySEDUtil#findMethod(ILaunchConfiguration)}.
     */
    @Test
    public void testFindMethod_ILaunchConfiguration() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeySEDUtilTest_testFindMethod_ILaunchConfiguration");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        IFolder banking = TestUtilsUtil.createFolder(srcFolder, "banking");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        // Get method
        IMethod method = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        // Create configuration
        ILaunchConfiguration configuration = KeySEDUtil.createConfiguration(method, null, null);
        assertNotNull(configuration);
        // Test null
        assertNull(KeySEDUtil.findMethod((ILaunchConfiguration)null));
        // Test method
        assertEquals(method, KeySEDUtil.findMethod(configuration));
    }
    
    /**
     * Tests {@link KeySEDUtil#getProjectValue(org.eclipse.debug.core.ILaunchConfiguration)}.
     */
    @Test
    public void testGetProjectValue_ILaunchConfiguration() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeySEDUtilTest_testGetProjectValue_ILaunchConfiguration");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        IFolder banking = TestUtilsUtil.createFolder(srcFolder, "banking");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        // Get method
        IMethod method = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        // Create configuration
        ILaunchConfiguration configuration = KeySEDUtil.createConfiguration(method, null, null);
        assertNotNull(configuration);
        // Test null
        assertEquals(StringUtil.EMPTY_STRING, KeySEDUtil.getProjectValue((ILaunchConfiguration)null));
        // Test method
        assertEquals(javaProject.getProject().getName(), KeySEDUtil.getProjectValue(configuration));
    }
    
    /**
     * Tests {@link KeySEDUtil#getTypeValue(org.eclipse.debug.core.ILaunchConfiguration)}.
     */
    @Test
    public void testGetTypeValue_ILaunchConfiguration() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeySEDUtilTest_testGetTypeValue_ILaunchConfiguration");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        IFolder banking = TestUtilsUtil.createFolder(srcFolder, "banking");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        // Get method
        IMethod method = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        // Create configuration
        ILaunchConfiguration configuration = KeySEDUtil.createConfiguration(method, null, null);
        assertNotNull(configuration);
        // Test null
        assertEquals(StringUtil.EMPTY_STRING, KeySEDUtil.getTypeValue((ILaunchConfiguration)null));
        // Test method
        assertEquals("banking.PayCard", KeySEDUtil.getTypeValue(configuration));
    }
    
    /**
     * Tests {@link KeySEDUtil#getMethodValue(org.eclipse.debug.core.ILaunchConfiguration)}.
     */
    @Test
    public void testGetMethodValue_ILaunchConfiguration() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeySEDUtilTest_testGetMethodValue_ILaunchConfiguration");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        IFolder banking = TestUtilsUtil.createFolder(srcFolder, "banking");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        // Get method
        IMethod method = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        // Create configuration
        ILaunchConfiguration configuration = KeySEDUtil.createConfiguration(method, null, null);
        assertNotNull(configuration);
        // Test null
        assertEquals(StringUtil.EMPTY_STRING, KeySEDUtil.getMethodValue((ILaunchConfiguration)null));
        // Test method
        assertEquals("charge(int)", KeySEDUtil.getMethodValue(configuration));
    }
    
    /**
     * Tests {@link KeySEDUtil#getProjectValue(org.key_project.sed.key.core.util.IMethod)}.
     */
    @Test
    public void testGetProjectValue_IMethod() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeySEDUtilTest_testGetProjectValue_IMethod");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        IFolder banking = TestUtilsUtil.createFolder(srcFolder, "banking");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        // Get method
        IMethod method = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        // Test null
        assertEquals(null, KeySEDUtil.getProjectValue((IMethod)null));
        // Test method
        assertEquals(javaProject.getProject().getName(), KeySEDUtil.getProjectValue(method));
    }
    
    /**
     * Tests {@link KeySEDUtil#getTypeValue(org.key_project.sed.key.core.util.IMethod)}.
     */
    @Test
    public void testGetTypeValue_IMethod() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeySEDUtilTest_testGetTypeValue_IMethod");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        IFolder banking = TestUtilsUtil.createFolder(srcFolder, "banking");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        // Get method
        IMethod method = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        // Test null
        assertEquals(null, KeySEDUtil.getTypeValue((IMethod)null));
        // Test method
        assertEquals("banking.PayCard", KeySEDUtil.getTypeValue(method));
    }
    
    /**
     * Tests {@link KeySEDUtil#getMethodValue(org.key_project.sed.key.core.util.IMethod)}.
     */
    @Test
    public void testGetMethodValue_IMethod() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeySEDUtilTest_testGetMethodValue_IMethod");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        IFolder banking = TestUtilsUtil.createFolder(srcFolder, "banking");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        // Get method
        IMethod method = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        // Test null
        assertEquals(null, KeySEDUtil.getMethodValue((IMethod)null));
        // Test method
        assertEquals("charge(int)", KeySEDUtil.getMethodValue(method));
    }
}