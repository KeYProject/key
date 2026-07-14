/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Set;
import javax.swing.text.Document;
import javax.swing.text.PlainDocument;

import de.uka.ilkd.key.control.KeYEnvironment;

import org.key_project.util.parsing.Location;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Verifies that the improved parser error messages and their source positions actually reach the
 * GUI error dialog ({@link IssueDialog}). The test exercises {@link IssueDialog#extractMessage} -
 * the method that turns a thrown exception into the message + location shown (and underlined) in
 * the dialog - without constructing the Swing dialog itself.
 *
 * @author Claude (improveErrorMessages)
 */
public class IssueDialogMessageTest {

    /**
     * Resolves the dialog's mark offset for {@code loc} via the same document line model the dialog
     * uses
     * ({@link IssueDialog#getOffsetFromLineColumn(Document, org.key_project.util.parsing.Position)}).
     * The document content equals {@code source}, so the returned offset indexes into it directly.
     */
    private static int offsetIn(String source, Location loc) throws Exception {
        Document doc = new PlainDocument();
        doc.insertString(0, source, null);
        return IssueDialog.getOffsetFromLineColumn(doc, loc.getPosition());
    }

    private static PositionedIssueString loadAndExtract(String content) throws Exception {
        Path tmp = Files.createTempFile("issueDialog", ".key");
        Files.writeString(tmp, content);
        try {
            KeYEnvironment.load(tmp);
            fail("expected the file to fail loading: " + content);
            throw new IllegalStateException("unreachable");
        } catch (Throwable t) {
            Set<PositionedIssueString> msgs = IssueDialog.extractMessage(t);
            assertEquals(1, msgs.size(), "expected a single issue");
            return msgs.iterator().next();
        } finally {
            Files.deleteIfExists(tmp);
        }
    }

    @Test
    public void javaBlockSyntaxErrorReachesDialog() throws Exception {
        String source = """
                \\problem {
                   \\<{ int i = ; }\\> true
                }
                """;
        var issue = loadAndExtract(source);
        // The hidden JavaParser reason is surfaced through the dialog ...
        assertTrue(issue.getText().contains("Java syntax error: unexpected"),
            "dialog message should expose the Java reason, but was: " + issue.getText());
        // ... and the location points at the modality in the .key file (line 2) for underlining.
        Location loc = issue.getLocation();
        assertNotNull(loc);
        assertEquals(2, loc.getPosition().line(),
            "the underline should point at the modality line in the .key file");
        assertNotNull(loc.getFileUri());

        // The block-relative Java error position is mapped back to the .key file, so the offset the
        // dialog uses to place the squiggly underline lands on the offending Java code ('=' before
        // the misplaced ';'), not on the modality token.
        int offset = offsetIn(source, loc);
        assertEquals('=', source.charAt(offset),
            "the underline offset should anchor on the offending Java code");
    }

    @Test
    public void brokenJavaSourceReachesDialog() throws Exception {
        // A broken Java file referenced via \javaSource goes through ProblemInitializer, which used
        // to collapse the error into "Failed to parse file". The dialog must still receive the
        // concrete message and a location pointing into the .java file (for the source preview).
        Path dir = Files.createTempDirectory("issueJavaSrc");
        Path java = dir.resolve("Broken.java");
        Files.writeString(java, "public class Broken {\n    int x = ;\n}\n");
        Path key = dir.resolve("problem.key");
        Files.writeString(key, "\\javaSource \".\";\n\n\\problem { true }\n");
        try {
            KeYEnvironment.load(key);
            fail("expected loading to fail");
        } catch (Throwable t) {
            Set<PositionedIssueString> msgs = IssueDialog.extractMessage(t);
            assertTrue(
                msgs.stream().anyMatch(m -> m.getText().contains("Java syntax error")),
                "the dialog should show the concrete Java error, but got: " + msgs);
            PositionedIssueString issue = msgs.stream()
                    .filter(m -> m.getLocation().getFileUri() != null
                            && m.getLocation().getFileUri().toString().endsWith("Broken.java"))
                    .findFirst().orElseThrow();
            assertEquals(2, issue.getLocation().getPosition().line(),
                "the underline should point at line 2 of Broken.java");
        } finally {
            Files.deleteIfExists(java);
            Files.deleteIfExists(key);
            Files.deleteIfExists(dir);
        }
    }
}
