/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.basic;

import java.io.File;
import javax.annotation.Nonnull;

import recoder.CrossReferenceServiceConfiguration;
import recoder.service.DefaultErrorHandler;

/**
 * Call example: java test.TransformationTests standard.tst collections.prj
 */
public class BasicTestsSuite {
    public static final String testConfig = "src/test/resources/basic/standard.tst";
    public static final String projectConfig = "src/test/resources/basic/collections.prj";
    private static CrossReferenceServiceConfiguration config;
    private static File projectFile;

    @Nonnull
    public static File getProjectFile() {
        if (projectFile == null) {
            init();
        }
        return projectFile;
    }

    @Nonnull
    public static CrossReferenceServiceConfiguration getConfig() {
        if (config == null) {
            init();
        }
        return config;
    }

    private static void init() {
        config = new CrossReferenceServiceConfiguration();
        // should use a specialized error handler instead
        // to check if errors are reported correctly
        config.getProjectSettings().setErrorHandler(new DefaultErrorHandler(0));
        projectFile = new File(projectConfig);
        if (!projectFile.exists()) {
            throw new IllegalArgumentException("Project File not found!");
        }
    }
}
