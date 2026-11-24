/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.util.ExceptionTools;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Load-level tests for the conversion of switch expressions, yields and switch patterns.
 */
class SwitchExpressionConversionTest {

    private static void assertLoads(Path dir, String className, String body)
            throws Exception {
        Path source = dir.resolve(className + ".java");
        Files.writeString(source, body);
        KeYEnvironment.load(source).dispose();
    }

    private static Throwable loadError(Path dir, String className, String body)
            throws Exception {
        Path source = dir.resolve(className + ".java");
        Files.writeString(source, body);
        try {
            KeYEnvironment.load(source).dispose();
            return null;
        } catch (Throwable t) {
            return t;
        }
    }

    @Test
    void loadsArrowSwitchExpression(@TempDir Path dir) throws Exception {
        assertLoads(dir, "C", """
                public class C {
                    int f(int x) { return switch (x) { case 1 -> 10; default -> 0; }; }
                }
                """);
    }

    @Test
    void loadsGroupedLabels(@TempDir Path dir) throws Exception {
        assertLoads(dir, "C", """
                public class C {
                    int f(int x) { return switch (x) { case 1, 2 -> 10; default -> 0; }; }
                }
                """);
    }

    @Test
    void loadsThrowArm(@TempDir Path dir) throws Exception {
        assertLoads(dir, "C", """
                public class C {
                    int f(int x) {
                        return switch (x) {
                            case 1 -> 10;
                            default -> throw new IllegalArgumentException();
                        };
                    }
                }
                """);
    }

    @Test
    void loadsCaseNullDefault(@TempDir Path dir) throws Exception {
        assertLoads(dir, "C", """
                public class C {
                    int f(String s) { return switch (s) { case null, default -> 0; }; }
                }
                """);
    }

    @Test
    void loadsTypePattern(@TempDir Path dir) throws Exception {
        assertLoads(dir, "C", """
                public class C {
                    int f(Object o) { return switch (o) { case Integer i -> i; default -> 0; }; }
                }
                """);
    }

    @Test
    void loadsGuardedTypePattern(@TempDir Path dir) throws Exception {
        assertLoads(dir, "C", """
                public class C {
                    int f(Object o) {
                        return switch (o) { case Integer i when i > 0 -> i; default -> 0; };
                    }
                }
                """);
    }

    @Test
    void loadsRecordPattern(@TempDir Path dir) throws Exception {
        assertLoads(dir, "C", """
                public class C {
                    record Point(int x, int y) {}
                    int f(Object o) {
                        return switch (o) {
                            case Point(int x, int y) -> x + y;
                            default -> 0;
                        };
                    }
                }
                """);
    }

    @Test
    void rejectsSwitchExpressionWithoutDefault(@TempDir Path dir) throws Exception {
        Throwable error = loadError(dir, "C", """
                public class C {
                    int f(int x) { return switch (x) { case 1 -> 10; }; }
                }
                """);
        assertThat(error).isNotNull();
        String messages = ExceptionTools.getMessages(error).stream()
                .map(it -> it.getText()).reduce("", (a, b) -> a + " " + b);
        assertThat(messages).containsIgnoringCase("default");
    }

    @Disabled("blocked on the jmlparser RAW-yield prerequisite (external repository)")
    @Test
    void loadsColonArmWithYield(@TempDir Path dir) throws Exception {
        assertLoads(dir, "C", """
                public class C {
                    int f(int x) { return switch (x) { case 1: yield 10; default: yield 0; }; }
                }
                """);
    }

    @Disabled("blocked on the jmlparser RAW-yield prerequisite (external repository)")
    @Test
    void loadsBlockArmWithYield(@TempDir Path dir) throws Exception {
        assertLoads(dir, "C", """
                public class C {
                    int f(int x) {
                        return switch (x) {
                            case 1 -> { int r = 10; yield r; }
                            default -> 0;
                        };
                    }
                }
                """);
    }
}
