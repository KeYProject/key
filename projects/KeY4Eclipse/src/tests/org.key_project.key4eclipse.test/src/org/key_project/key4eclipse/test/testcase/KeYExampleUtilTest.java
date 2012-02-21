package org.key_project.key4eclipse.test.testcase;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.Properties;

import junit.framework.TestCase;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Platform;
import org.junit.Test;
import org.key_project.key4eclipse.test.Activator;
import org.key_project.key4eclipse.util.KeYExampleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.util.TestUtilsUtil;
import org.osgi.framework.Bundle;

/**
 * Contains tests for {@link KeYExampleUtil}.
 * @author Martin Hentschel
 */
public class KeYExampleUtilTest extends TestCase {
    /**
     * Tests {@link KeYExampleUtil#getLocalKeYHomeDirectory()}.
     */
    @Test
    public void testGetLocalKeYHomeDirectory() throws IOException {
        // Get value
        String localExampleDir = KeYExampleUtil.getLocalKeYHomeDirectory();
        // Compare value
        assertEquals(getLocalPropertyValue("key.rep"), localExampleDir);
    }

    /**
     * Tests {@link KeYExampleUtil#getLocalKeYExtraLibsDirectory()}.
     */
    @Test
    public void testGetLocalKeYExtraLibsDirectory() throws IOException {
        // Get value
        String localExampleDir = KeYExampleUtil.getLocalKeYExtraLibsDirectory();
        // Compare value
        assertEquals(getLocalPropertyValue("ext.dir"), localExampleDir);
    }

    /**
     * Tests {@link KeYExampleUtil#getLocalExampleDirectory()}.
     */
    @Test
    public void testGetLocalExampleDirectory() throws IOException {
        // Get value
        String localExampleDir = KeYExampleUtil.getLocalExampleDirectory();
        // Compare value
        assertEquals(getLocalPropertyValue("key.rep") + File.separator + "examples" + File.separator + "heap", localExampleDir);
    }
    
    /**
     * Tests {@link KeYExampleUtil#getLocalPropertyValue(String)}.
     */
    @Test
    public void testGetLocalPropertyValue() throws IOException {
        // Test null
        assertNull(KeYExampleUtil.getLocalPropertyValue(null));
        // Test valid keys
        assertEquals(getLocalPropertyValue("key.rep"), KeYExampleUtil.getLocalPropertyValue("key.rep"));
        assertEquals(getLocalPropertyValue("ext.dir"), KeYExampleUtil.getLocalPropertyValue("ext.dir"));
        // Test invalid key
        assertEquals(getLocalPropertyValue("INVALID"), KeYExampleUtil.getLocalPropertyValue("INVALID"));
    }
    
    /**
     * Tests {@link KeYExampleUtil#getLocalProperties()}.
     */
    @Test
    public void testGetLocalProperties() throws IOException {
        Properties expected = getLocalProperties();
        Properties actual = KeYExampleUtil.getLocalProperties();
        assertEquals(expected.size(), actual.size());
        Enumeration<?> keys = expected.propertyNames();
        while (keys.hasMoreElements()) {
            Object key = keys.nextElement();
            assertTrue(key instanceof String);
            assertTrue(actual.containsKey(key));
            assertEquals(expected.getProperty((String)key), actual.getProperty((String)key));
        }
    }
    
    /**
     * Returns the local property value.
     * @param key The key.
     * @return The value.
     * @throws IOException Occurred exception.
     */
    protected String getLocalPropertyValue(String key) throws IOException {
        Properties props = getLocalProperties();
        return props != null ? props.getProperty(key) : null;
    }
    
    /**
     * Returns all local properties.
     * @return The local properties.
     * @throws IOException Occurred exception.
     */
    protected Properties getLocalProperties() throws IOException {
        Bundle bundle = Platform.getBundle("org.key_project.key4eclipse");
        if (bundle != null) {
            URL entry = bundle.getEntry("customTargets.properties");
            if (entry != null) {
                InputStream in = null;
                try {
                    in = entry.openStream();
                    Properties properties = new Properties();
                    properties.load(in);
                    return properties;
                }
                finally {
                    if (in != null) {
                        in.close();
                    }
                }
            }
            else {
                return null;
            }
        }
        else {
            return null;
        }
    }
    
    /**
     * Tests {@link KeYExampleUtil#updateExampleDirectory(String, String, String, String, String)}.
     */
    @Test
    public void testUpdateExampleDirectory() throws CoreException, IOException {
        // Create target to use as example.
        IProject project = TestUtilsUtil.createProject("KeYExampleUtilTest_testUpdateExampleDirectory");
        File projectLocation = ResourceUtil.getLocation(project);
        File exampleDir = new File(projectLocation, "example");
        File exampleFile = new File(projectLocation, "example.properties");
        assertFalse(exampleDir.exists());
        assertFalse(exampleFile.exists());
        // Test initial creation
        KeYExampleUtil.updateExampleDirectory("1", Activator.PLUGIN_ID, "data/ExampleContent1", exampleFile.getAbsolutePath(), exampleDir.getAbsolutePath());
        assertExampleDirectory(exampleDir, exampleFile, "1", "ExampleFile1.txt");
        // Test same version again
        KeYExampleUtil.updateExampleDirectory("1", Activator.PLUGIN_ID, "data/ExampleContent1", exampleFile.getAbsolutePath(), exampleDir.getAbsolutePath());
        assertExampleDirectory(exampleDir, exampleFile, "1", "ExampleFile1.txt");
        // Test different version
        KeYExampleUtil.updateExampleDirectory("2", Activator.PLUGIN_ID, "data/ExampleContent2", exampleFile.getAbsolutePath(), exampleDir.getAbsolutePath());
        assertExampleDirectory(exampleDir, exampleFile, "2", "ExampleFile2.txt", "ExampleFile3.txt");
        // Test different version again
        KeYExampleUtil.updateExampleDirectory("2", Activator.PLUGIN_ID, "data/ExampleContent2", exampleFile.getAbsolutePath(), exampleDir.getAbsolutePath());
        assertExampleDirectory(exampleDir, exampleFile, "2", "ExampleFile2.txt", "ExampleFile3.txt");
        // Test initial version again
        KeYExampleUtil.updateExampleDirectory("1", Activator.PLUGIN_ID, "data/ExampleContent1", exampleFile.getAbsolutePath(), exampleDir.getAbsolutePath());
        assertExampleDirectory(exampleDir, exampleFile, "1", "ExampleFile1.txt");
    }
    
    /**
     * Makes sure that the correct example content exists.
     * @param exampleDir The example directory to check.
     * @param exampleFile The example file to check.
     * @param expectedVersion The expected version.
     * @param expectedFiles The expected files in the example directory.
     * @throws IOException Occurred Exception.
     */
    protected void assertExampleDirectory(File exampleDir, 
                                          File exampleFile, 
                                          String expectedVersion, 
                                          String... expectedFiles) throws IOException {
        // Test example directory
        assertTrue(exampleDir.exists());
        File[] files = exampleDir.listFiles();
        assertNotNull(files);
        Arrays.sort(files);
        assertEquals(expectedFiles.length, files.length);
        for (int i = 0; i < files.length; i++) {
            assertEquals(files[i].getName(), expectedFiles[i]);
            assertEquals(expectedFiles[i], IOUtil.readFrom(new FileInputStream(files[i])));
        }
        // Test example file
        assertTrue(exampleFile.exists());
        Properties properties = new Properties();
        properties.load(new FileInputStream(exampleFile));
        assertEquals(expectedVersion, properties.get(KeYExampleUtil.VERSION_KEY));
    }
}
