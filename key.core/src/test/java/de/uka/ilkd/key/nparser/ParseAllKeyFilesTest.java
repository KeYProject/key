/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.stream.Collectors;

import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * @author Alexander Weigl
 * @version 1 (13.09.19)
 */
@Tag("interactive")
@Disabled
public class ParseAllKeyFilesTest {
    public static Collection<Path> getFiles() throws IOException {
        try (var s = Files.walk(HelperClassForTests.TESTCASE_DIRECTORY.toPath())) {
            return s.filter(file -> Files.isRegularFile(file) && file.toString().endsWith(".key"))
                    .collect(Collectors.toList());
        }
    }

    @ParameterizedTest
    @MethodSource("getFiles")
    void parse(Path file) throws IOException {
        KeyAst.File ctx = ParsingFacade.parseFile(file);
        assertNull(ctx.ctx.exception);
    }
}
