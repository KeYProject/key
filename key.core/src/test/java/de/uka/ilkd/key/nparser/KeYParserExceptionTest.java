/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;
import java.util.stream.Stream;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.util.ParserExceptionTest;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * This test case is used to ensure that errors in KeY files are reported
 * with a reasonable error message and the right position pointing
 * into the file.
 *
 * To add a test case, locate the "exceptional" directory in the resources
 * (below the directory for this package here) and add a .key file
 * that contains an error that should be presented to the user (like syntax
 * error, unresolved names, ...)
 *
 * See README.md in said directory for information on the meta-data inside
 * the files.
 *
 * @author Mattias Ulbrich
 */
public class KeYParserExceptionTest extends ParserExceptionTest {

    /*
     * Usually a directory is scanned for files to operate on.
     * If this here is not null, this file name (referring to the resources
     * directory) will be loaded.
     */
    private static final String FIX_FILE = null; // "conflict.java";

    /// FIXME weigl: this seems to be broken and should always result into NPE.
    public static Stream<Arguments> getFiles() throws URISyntaxException, IOException {
        URL fileURL = KeYParserExceptionTest.class.getResource("exceptional");
        return getFiles(FIX_FILE, fileURL, ".key");
    }


    @ParameterizedTest(name = "case {1}")
    @MethodSource("getFiles")
    public void testParseAndInterpret(Path file, Path localFilename) throws Exception {
        parseAndInterpret(file);
    }

    @Override
    protected void tryLoadFile(Path file) throws Exception {
        KeYEnvironment.load(file);
    }
}
