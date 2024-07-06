/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.stream.Stream;

import de.uka.ilkd.key.nparser.format.KeyFormatFacade;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

/**
 * @author Alexander Weigl
 * @version 1 (14.07.24)
 */
public class CheckAll {
    @TestFactory
    public Stream<DynamicTest> checkAllKeYFiles() throws IOException {
        var s = Files.walk(Paths.get(".."));
        return s.filter(it -> it.getFileName().toString().endsWith(".key"))
                .map(it -> DynamicTest.dynamicTest(it.getFileName().toString(),
                    () -> Assertions.assertTrue(KeyFormatFacade.checkFile(it))));
    }
}
