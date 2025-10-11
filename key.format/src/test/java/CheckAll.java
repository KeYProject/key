/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

import org.antlr.v4.runtime.CharStreams;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.stream.Stream;

import static de.uka.ilkd.key.nparser.format.KeyFileFormatter.format;

/**
 * @author Alexander Weigl
 * @version 1 (14.07.24)
 */
public class CheckAll {
    @TestFactory
    public Stream<DynamicTest> checkAllKeYFiles() throws IOException {
        final var rules = Paths.get("../key.core/src/main/resources/de/uka/ilkd/key/proof/rules")
                .toAbsolutePath();
        System.out.println(Files.exists(rules));
        try (var s = Files.walk(rules)) {
            var sq = s.toList();
            return sq.stream().filter(it -> it.getFileName().toString().endsWith(".key"))
                    .map(it -> DynamicTest.dynamicTest(it.getFileName().toString(),
                            () -> {
                                var formatted = format(CharStreams.fromPath(it));
                                var content = Files.readString(it);
                                Assertions.assertEquals(content, formatted);
                            }));
        }
    }
}
