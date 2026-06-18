/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.javac;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ExecutionException;
import javax.tools.ToolProvider;

import de.uka.ilkd.key.gui.PositionedIssueString;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * @author Alexander Weigl
 * @version 1 (29.01.23)
 */
class JavaCompilerCheckFacadeTest {

    /**
     * Runs the javac check over a single given Java source and returns the diagnostics. Skips the
     * test if no system Java compiler is available in the current runtime.
     */
    private static List<PositionedIssueString> checkSource(String fileName, String content)
            throws Exception {
        Assumptions.assumeTrue(ToolProvider.getSystemJavaCompiler() != null,
            "no system Java compiler available");
        Path dir = Files.createTempDirectory("javac");
        Path src = dir.resolve(fileName);
        Files.writeString(src, content);
        try {
            return JavaCompilerCheckFacade
                    .check(null, Collections.emptyList(), dir, new JavacSettings()).get();
        } finally {
            Files.deleteIfExists(src);
            Files.deleteIfExists(dir);
        }
    }

    @Test
    void reportsDuplicateField() throws Exception {
        var diags = checkSource("Dup.java",
            "public class Dup {\n    int size = 0;\n    int size = 0;\n}\n");
        assertTrue(diags.stream().anyMatch(d -> d.text.contains("already defined")),
            "duplicate field should be reported, but got: " + diags);
        var dup = diags.stream().filter(d -> d.text.contains("already defined")).findFirst()
                .orElseThrow();
        assertEquals(3, dup.location.getPosition().line(),
            "the duplicate is on line 3, but location was: " + dup.location);
        assertTrue(dup.location.fileUri() != null
                && dup.location.fileUri().toString().endsWith("Dup.java"));
    }

    @Test
    void reportsTypeIncompatibility() throws Exception {
        var diags = checkSource("Typo.java",
            "public class Typo {\n    int size = \"zero\";\n}\n");
        assertTrue(diags.stream().anyMatch(d -> d.text.contains("incompatible types")),
            "type incompatibility should be reported, but got: " + diags);
        var err = diags.stream().filter(d -> d.text.contains("incompatible types")).findFirst()
                .orElseThrow();
        assertEquals(2, err.location.getPosition().line(),
            "the type error is on line 2, but location was: " + err.location);
    }

    @Test
    void compile1() throws ExecutionException, InterruptedException {
        File src = new File("examples/firstTouch/06-BinarySearch/src/").getAbsoluteFile();
        System.out.println(src);
        var promise =
            JavaCompilerCheckFacade.check(null, Collections.emptyList(),
                src.toPath(), new JavacSettings());
        var result = promise.get();
        assertTrue(result.isEmpty());
    }

    @Test
    void compileExternal() throws ExecutionException, InterruptedException {
        File src = new File("examples/firstTouch/06-BinarySearch/src/").getAbsoluteFile();
        System.out.println(src);
        var promise =
            JavaCompilerCheckFacade.checkExternally(null, Collections.emptyList(),
                src.toPath(), new JavacSettings());
        var result = promise.get();
        assertTrue(result.isEmpty());
    }
}
