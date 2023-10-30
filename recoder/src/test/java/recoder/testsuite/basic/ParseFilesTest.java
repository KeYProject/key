/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.basic;

import java.io.IOException;

import org.junit.Test;
import recoder.ParserException;
import recoder.io.DefaultProjectFileIO;

import static recoder.testsuite.basic.BasicTestsSuite.getConfig;
import static recoder.testsuite.basic.BasicTestsSuite.getProjectFile;

public class ParseFilesTest {
    @Test
    public void testParseFiles() throws IOException, ParserException {
        getConfig().getSourceFileRepository().getCompilationUnitsFromFiles(
            new DefaultProjectFileIO(getConfig(), getProjectFile()).load());
    }
}
