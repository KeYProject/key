/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless tests for the taclet-management operations, loading a small proof without the Swing
 * GUI via {@link KeYEnvironment}.
 */
class TacletOperationsTest {

    private static final Path LOCATION =
        Path.of("src/test/resources/org/key_project/key/llm/tacletops.key");

    private KeYEnvironment<?> env;
    private Proof proof;

    @BeforeEach
    void setUp() throws ProblemLoaderException {
        Assumptions.assumeTrue(Files.exists(LOCATION), "File " + LOCATION + " not found.");
        env = KeYEnvironment.load(LOCATION);
        proof = env.getLoadedProof();
    }

    @AfterEach
    void tearDown() {
        if (env != null) {
            env.dispose();
        }
    }

    @Test
    void listTacletsContainsStandardRules() {
        var listing = TacletOperations.listTaclets(proof, null);
        assertTrue(listing.contains("impRight"), "listing should contain impRight:\n" + listing);
        assertTrue(listing.contains("andLeft"), "listing should contain andLeft:\n" + listing);
        assertTrue(listing.matches("(?s)\\d+ taclet\\(s\\):.*"),
            "listing should start with a count:\n" + listing);
    }

    @Test
    void listTacletsFiltersByName() {
        var filtered = TacletOperations.listTaclets(proof, "imp");
        var all = TacletOperations.listTaclets(proof, null);
        assertTrue(all.split("\n").length > filtered.split("\n").length,
            "filter must narrow the listing");
        for (var line : filtered.lines().filter(l -> l.startsWith("- ")).toList()) {
            assertTrue(line.toLowerCase().contains("imp"),
                "every filtered entry must match: " + line);
        }
    }

    @Test
    void listTacletOptionsListsCategoriesAndSelection() {
        var options = TacletOperations.listTacletOptions(proof);
        assertTrue(options.contains("programRules"),
            "options should list programRules:\n" + options);
        assertTrue(options.contains("programRules: "),
            "options should show the selection:\n" + options);
    }

    @Test
    void exportTacletProducesParseableDeclaration() {
        var exported = TacletOperations.exportTaclet(proof, "impRight");
        assertTrue(exported.contains("impRight"), "export must contain the name:\n" + exported);
        assertTrue(exported.contains("\\find"), "export must contain \\find:\n" + exported);
        // a re-registration of the same taclet must be reported as duplicate
        var dup = TacletOperations.addTaclet(proof, exported);
        assertTrue(dup.startsWith("Error: taclet \"impRight\" already exists"), dup);
    }

    @Test
    void addAndRemoveTacletRoundTrip() {
        var exported = TacletOperations.exportTaclet(proof, "impRight");
        var renamed = exported.replaceFirst("impRight", "impRightCopy");
        var added = TacletOperations.addTaclet(proof, renamed);
        assertTrue(added.contains("Registered taclet \"impRightCopy\""), added);
        assertTrue(TacletOperations.listTaclets(proof, null).contains("impRightCopy"));

        var exportedCopy = TacletOperations.exportTaclet(proof, "impRightCopy");
        assertTrue(exportedCopy.contains("impRightCopy"),
            "the added taclet must be exportable:\n" + exportedCopy);

        var removed = TacletOperations.removeTaclet(proof, "impRightCopy");
        assertTrue(removed.contains("Removed taclet \"impRightCopy\""), removed);
        assertFalse(TacletOperations.listTaclets(proof, null).contains("impRightCopy"));
        assertTrue(TacletOperations.removeTaclet(proof, "impRightCopy").startsWith("Error:"),
            "second removal must fail");
    }

    @Test
    void addTacletAcceptsLegacyKeywordAndRejectsInvalidSyntax() {
        var exported = TacletOperations.exportTaclet(proof, "andLeft");
        var withKeyword = "\\taclet " + exported.replaceFirst("andLeft", "andLeftKey");
        var added = TacletOperations.addTaclet(proof, withKeyword);
        assertTrue(added.contains("Registered"), "\\taclet keyword must be tolerated:\n" + added);
        TacletOperations.removeTaclet(proof, "andLeftKey");

        assertTrue(TacletOperations.addTaclet(proof, "this is not a taclet").startsWith("Error:"));
    }

    @Test
    void exportTacletsBulkExportsWithCap() {
        var bulk = TacletOperations.exportTaclets(proof, null);
        assertTrue(bulk.matches("(?s)\\d+ taclet\\(s\\):.*"),
            "bulk export should start with a count:\n" + bulk);
        assertTrue(bulk.contains("\\find"), "bulk export should contain declarations:\n" + bulk);
        assertTrue(
            TacletOperations.exportTaclets(proof, "no_such_taclet_x").contains("(no taclets"),
            "empty filter should report no matches");
    }

    @Test
    void unknownTacletNamesProduceErrors() {
        assertTrue(TacletOperations.exportTaclet(proof, "no_such_taclet").startsWith("Error:"));
        assertTrue(TacletOperations.removeTaclet(proof, "no_such_taclet").startsWith("Error:"));
    }
}
