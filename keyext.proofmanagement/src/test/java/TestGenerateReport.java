/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
import java.io.IOException;
import java.nio.file.Files;

import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.proofmanagement.Main;

import org.junit.jupiter.api.Test;

/**
 * @author Alexander Weigl
 * @version 1 (6/16/25)
 */
public class TestGenerateReport {
    @Test
    void test() throws IOException {
        var testDir = HelperClassForTests.TESTCASE_DIRECTORY.resolve("proofBundle")
                .toAbsolutePath().normalize();
        var file = Files.createTempFile("report", ".html");
        Main.check(true, true, true, true, testDir, file);
    }
}
