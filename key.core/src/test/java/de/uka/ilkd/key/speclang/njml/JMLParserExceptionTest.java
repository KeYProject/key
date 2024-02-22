/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;
import java.util.Properties;
import java.util.stream.Stream;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.util.ParserExceptionTest;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * This test case is used to ensure that errors in JML (and perhaps also in Java)
 * are reported with a reasonable error message and the right position pointing
 * into the file.
 *
 * To add a test case, locate the "exceptional" directory in the resources
 * (below the directory for this package here) and add your single Java file
 * that contains an error that should be presented to the user (like syntax
 * error, unresolved names, ...)
 *
 * See README.md in said directory for information on the meta-data inside
 * the Java files.
 *
 * @author Mattias Ulbrich
 */
public class JMLParserExceptionTest extends ParserExceptionTest {

    /*
     * Usually a directory is scanned for files to operate on.
     * If this here is not null, this file name (referring to the resources
     * directory) will be loaded.
     */
    private static final String FIX_FILE = null; // "SomeSpecificFile.java";

    public static Stream<Arguments> getFiles() throws URISyntaxException, IOException {
        URL fileURL = JMLParserExceptionTest.class.getResource("exceptional");
        return ParserExceptionTest.getFiles(FIX_FILE, fileURL, ".java");
    }


    @ParameterizedTest(name = "case {1}")
    @MethodSource("getFiles")
    public void testParseAndInterpret(Path file, Path localFilename) throws Exception {
        parseAndInterpret(file);
    }

    @Override
    protected void tryLoadFile(Path file) throws Exception {
        ProblemLoaderControl control = new DefaultUserInterfaceControl(null);
        AbstractProblemLoader pl = new SingleThreadProblemLoader(file.toFile(), null, null,
            null, AbstractProfile.getDefaultProfile(), false,
            control, false, new Properties());
        pl.setLoadSingleJavaFile(true);
        pl.load();
    }
}
