package de.uka.ilkd.key.suite.util;

import org.junit.Assert;
import org.key_project.util.helper.FindResources;

import java.io.File;

public class HelperClassForTestgenTests {
    public static final File TESTCASE_DIRECTORY = FindResources.getTestCasesDirectory();

    static {
        Assert.assertNotNull("Could not find test case directory", TESTCASE_DIRECTORY);
    }
}
