/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.ExceptionTools;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * End-to-end test for the reporting of errors in a Java source referenced via {@code \javaSource}.
 * <p>
 * This exercises the path through {@link ProblemInitializer#readJava} and
 * {@link de.uka.ilkd.key.java.JavaService#readCompilationUnits} - i.e. classes that are "further
 * away" from the pure parser - and ensures that the concrete problem (message + location pointing
 * into the offending {@code .java} file) is preserved instead of being collapsed into the generic
 * "Failed to parse file" wrapper.
 *
 * @author Claude (improveErrorMessages)
 */
public class JavaSourceErrorReportingTest {

    @Test
    public void brokenJavaSourceReportsConcreteMessageAndLocation() throws Exception {
        Path dir = Files.createTempDirectory("javasrcerr");
        Path java = dir.resolve("Broken.java");
        // The field initializer is missing its expression -> syntax error on line 2.
        Files.writeString(java, "public class Broken {\n    int x = ;\n}\n");
        Path key = dir.resolve("problem.key");
        Files.writeString(key, "\\javaSource \".\";\n\n\\problem { true }\n");

        try {
            KeYEnvironment.load(key);
            fail("expected loading to fail because of the broken Java source");
        } catch (Throwable t) {
            List<PositionedString> messages = ExceptionTools.getMessages(t);
            assertFalse(messages.isEmpty(), "at least one problem must be reported");
            // The concrete reason is surfaced (not just "Failed to parse file").
            assertTrue(messages.stream().anyMatch(m -> m.getText().contains("Java syntax error")),
                "expected a concrete Java syntax error, but got: " + messages);
            // ... and it points into Broken.java at the offending line.
            PositionedString first = messages.get(0);
            assertNotNull(first.getLocation().getFileUri());
            assertTrue(first.getLocation().getFileUri().toString().endsWith("Broken.java"),
                "location should point into Broken.java, but was: " + first.getLocation());
            assertEquals(2, first.getLocation().getPosition().line(),
                "the error is on line 2 of Broken.java");
        } finally {
            Files.deleteIfExists(java);
            Files.deleteIfExists(key);
            Files.deleteIfExists(dir);
        }
    }
}
