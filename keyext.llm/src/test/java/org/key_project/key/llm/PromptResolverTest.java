/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import org.key_project.key.llm.PromptResolver.Context;
import org.key_project.key.llm.PromptResolver.Result;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the {@code $token}/{\@file}//directive} resolution in {@link PromptResolver}.
 * <p>
 * These tests avoid touching the user's home directory: with no proof loaded all proof-dependent
 * tokens and file references resolve to explicit placeholders, and the prompt/skill libraries fall
 * back to empty when the config directory does not exist.
 */
class PromptResolverTest {

    private LlmSession session;

    @BeforeEach
    void setUp() {
        session = new LlmSession("https://example.invalid", "token", "model");
    }

    /** No proof, no node: nothing that requires proof state. */
    private static Context noProof() {
        return new Context() {
            @Override
            public de.uka.ilkd.key.proof.Proof proof() {
                return null;
            }

            @Override
            public de.uka.ilkd.key.proof.Node node() {
                return null;
            }
        };
    }

    @Test
    void unknownTokenBecomesPlaceholder() {
        Result r = PromptResolver.resolve("summarize $seq", session, noProof());
        assertTrue(r.text().contains("[unknown token $seq]"), r.text());
        assertNull(r.skillName());
        assertTrue(r.warnings().isEmpty());
    }

    @Test
    void selectedFilesWithoutFiles() {
        Result r = PromptResolver.resolve("use $selectedFiles", session, noProof());
        assertEquals("use (no files selected)", r.text());
    }

    @Test
    void selectedFilesListsUris() throws Exception {
        session.setSelectedFiles(java.util.Set.of(new java.net.URI("file:///tmp/a.java"),
            new java.net.URI("file:///tmp/b.java")));
        Result r = PromptResolver.resolve("read $selectedFiles", session, noProof());
        assertTrue(r.text().contains("file:///tmp/a.java"), r.text());
        assertTrue(r.text().contains("file:///tmp/b.java"), r.text());
    }

    @Test
    void fileReferenceWithoutProof() {
        Result r = PromptResolver.resolve("see @src/Main.java", session, noProof());
        assertTrue(r.text().contains("(no proof loaded)"), r.text());
    }

    @Test
    void unknownSkillAddsWarningAndKeepsText() {
        Result r = PromptResolver.resolve("please /skill:nope do this", session, noProof());
        assertEquals("please /skill:nope do this", r.text());
        assertNull(r.skillName());
        assertEquals(1, r.warnings().size());
        assertTrue(r.warnings().get(0).contains("nope"));
    }

    @Test
    void unknownPromptBecomesPlaceholderWithWarning() {
        Result r = PromptResolver.resolve("start with /prompt:nope", session, noProof());
        assertTrue(r.text().contains("[unknown prompt: nope]"), r.text());
        assertTrue(r.warnings().stream().anyMatch(w -> w.contains("nope")));
    }

    @Test
    void skillsListingWorksWithoutConfigDirectory() {
        Result r = PromptResolver.resolve("list /skills please", session, noProof());
        assertTrue(r.text().contains("(none defined)") || r.text().contains("- "),
            "unexpected listing: " + r.text());
    }

    @Test
    void pureLibraryDirectivesAreDetected() {
        assertTrue(PromptResolver.isPureLibraryDirective("/skills"));
        assertTrue(PromptResolver.isPureLibraryDirective("/prompts"));
        assertTrue(PromptResolver.isPureLibraryDirective("/skills /prompts /skills"));
        assertTrue(PromptResolver.isPureLibraryDirective("  /skills  \n"));
        assertFalse(PromptResolver.isPureLibraryDirective("/skill:optics"));
        assertFalse(PromptResolver.isPureLibraryDirective("list /skills please"));
        assertFalse(PromptResolver.isPureLibraryDirective("/skills and more"));
        assertFalse(PromptResolver.isPureLibraryDirective(""));
        assertFalse(PromptResolver.isPureLibraryDirective("   "));
    }

    @Test
    void pureListingDirectiveResolvesToRenderedListing() {
        Result r = PromptResolver.resolve("/skills", session, noProof());
        assertTrue(r.text().contains("(none defined)") || r.text().contains("- "),
            "unexpected listing: " + r.text());
        assertNull(r.skillName());
        assertTrue(r.warnings().isEmpty());
    }

    @Test
    void provableTokensArePlaceholdersWithoutProof() {
        // $computePath works without a proof (falls back to "no selected node")
        Result r = PromptResolver.resolve("path: $computePath", session, noProof());
        assertFalse(r.text().contains("$computePath"), r.text());
    }
}
