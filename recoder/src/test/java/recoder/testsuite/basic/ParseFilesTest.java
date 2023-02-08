/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package recoder.testsuite.basic;

import org.junit.Test;
import recoder.ParserException;
import recoder.io.DefaultProjectFileIO;

import java.io.IOException;

import static recoder.testsuite.basic.BasicTestsSuite.getConfig;
import static recoder.testsuite.basic.BasicTestsSuite.getProjectFile;

public class ParseFilesTest {
    @Test
    public void testParseFiles() throws IOException, ParserException {
        getConfig().getSourceFileRepository().getCompilationUnitsFromFiles(
            new DefaultProjectFileIO(getConfig(), getProjectFile()).load());
    }
}
