package org.key_project.sed.key.core.test.testcase;

import java.util.List;

import junit.framework.TestCase;

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
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link KeySEDUtil}.
 * @author Martin Hentschel
 */
public class KeySEDUtilTest extends TestCase {
    /**
     * Tests {@link KeySEDUtil#searchLaunchConfigurations(IMethod)}.
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
        ILaunchConfiguration firstConfiguration = KeySEDUtil.createConfiguration(firstMethod);
        assertNotNull(firstConfiguration);
        // Create second and third configuration
        ILaunchConfiguration secondConfiguration = KeySEDUtil.createConfiguration(secondMethod);
        assertNotNull(secondConfiguration);
        ILaunchConfiguration thirdConfiguration = KeySEDUtil.createConfiguration(secondMethod);
        assertNotNull(thirdConfiguration);
        // Test null
        List<ILaunchConfiguration> result = KeySEDUtil.searchLaunchConfigurations(null);
        assertNotNull(result);
        assertEquals(0, result.size());
        // Search configuration for first method
        result = KeySEDUtil.searchLaunchConfigurations(firstMethod);
        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals(firstConfiguration, result.get(0));
        // Search configurations for second method
        result = KeySEDUtil.searchLaunchConfigurations(secondMethod);
        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals(secondConfiguration, result.get(0));
        assertEquals(thirdConfiguration, result.get(1));
    }
    
    /**
     * Tests {@link KeySEDUtil#createConfiguration(IMethod)}.
     */
    @Test
    public void testCreateConfiguration() throws CoreException, InterruptedException {
        // Create projects with test content
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("KeySEDUtilTest_testCreateConfiguration");
        IFolder srcFolder = javaProject.getProject().getFolder("src");
        IFolder banking = TestUtilsUtil.createFolder(srcFolder, "banking");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        // Get method
        IMethod method = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        // Create configuration
        ILaunchConfiguration configuration = KeySEDUtil.createConfiguration(method);
        assertNotNull(configuration);
        assertEquals(javaProject.getProject().getName(), KeySEDUtil.getProjectValue(configuration));
        assertEquals("banking.PayCard", KeySEDUtil.getTypeValue(configuration));
        assertEquals("charge(int)", KeySEDUtil.getMethodValue(configuration));
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
        ILaunchConfiguration configuration = KeySEDUtil.createConfiguration(method);
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
        ILaunchConfiguration configuration = KeySEDUtil.createConfiguration(method);
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
        ILaunchConfiguration configuration = KeySEDUtil.createConfiguration(method);
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
        ILaunchConfiguration configuration = KeySEDUtil.createConfiguration(method);
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
        ILaunchConfiguration configuration = KeySEDUtil.createConfiguration(method);
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
