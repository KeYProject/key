package de.uka.ilkd.key.suite.util;

import org.key_project.util.helper.FindResources;

import java.io.File;

import static org.junit.jupiter.api.Assertions.assertNotNull;

public class HelperClassForTestgenTests {
    public static final File TESTCASE_DIRECTORY = FindResources.getTestCasesDirectory();

    static {
        assertNotNull(TESTCASE_DIRECTORY, "Could not find test case directory");
    }
}
