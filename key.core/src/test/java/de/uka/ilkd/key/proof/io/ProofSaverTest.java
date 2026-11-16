/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.prover.sequent.Sequent;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ProofSaverTest {

    // the deprecated Proof constructor taking a Sequent is the one exercised by the saver
    @SuppressWarnings("deprecation")
    void testSaveProblemToFile(String content) throws IOException {
        Services services = TacletForTests.services();
        KeyIO io = new KeyIO(services);
        KeyIO.Loader loader = io.load(content);
        Sequent seq = loader.parseFile().loadProblem().getProblem();
        final InitConfig initConfig =
            new InitConfig(new Services(AbstractProfile.getDefaultProfile()));
        Proof proof = new Proof("test", seq, null, initConfig.createTacletIndex(),
            initConfig.createBuiltInRuleIndex(), initConfig);
        Path file = Files.createTempFile("proofSaveTest", ".key");
        String status = new ProofSaver(proof, file).save();
        assertNull(status);

        KeyIO io2 = new KeyIO(services);
        KeyIO.Loader loader2 = io2.load(content);
        Sequent seq2 = loader2.parseFile().loadProblem().getProblem();

        assertEquals(seq, seq2);

        Files.deleteIfExists(file);
    }

    @Test
    void saveTermProblemToFile() throws IOException {
        String content = "\\problem { true }";
        testSaveProblemToFile(content);
    }

    @Test
    void saveSequentProblemToFile() throws IOException {
        String content = "\\problem { true, false ==> false, false }";
        testSaveProblemToFile(content);
    }

    @Test
    void saveWithClosedMarkerHeader() throws IOException {
        Services services = TacletForTests.services();
        KeyIO io = new KeyIO(services);
        KeyIO.Loader loader = io.load("\\problem { true }");
        Sequent seq = loader.parseFile().loadProblem().getProblem();
        final InitConfig initConfig =
            new InitConfig(new Services(AbstractProfile.getDefaultProfile()));
        Proof proof = new Proof("test", seq, null, initConfig, null);
        Path file = Files.createTempFile("proofSaveTest", ".key");

        String status = ProofSaver.saveToFile(file, proof, ProofSaver.marker(true, 0));
        assertNull(status);

        String firstLine = Files.readAllLines(file).get(0);
        assertEquals("// KEY_PROOF_STATUS closed 0", firstLine);

        Files.deleteIfExists(file);
    }

    @Test
    void saveWithoutHeaderKeepsProfileFirstLine() throws IOException {
        Services services = TacletForTests.services();
        KeyIO io = new KeyIO(services);
        KeyIO.Loader loader = io.load("\\problem { true }");
        Sequent seq = loader.parseFile().loadProblem().getProblem();
        final InitConfig initConfig =
            new InitConfig(new Services(AbstractProfile.getDefaultProfile()));
        Proof proof = new Proof("test", seq, null, initConfig, null);
        Path file = Files.createTempFile("proofSaveTest", ".key");

        String status = new ProofSaver(proof, file).save();
        assertNull(status);

        String firstLine = Files.readAllLines(file).get(0);
        assertTrue(firstLine.startsWith("\\profile "),
            "first line should be \\profile without header");

        Files.deleteIfExists(file);
    }

    @Test
    void markerProducesExpectedStrings() {
        assertEquals("// KEY_PROOF_STATUS closed 0", ProofSaver.marker(true, 0));
        assertEquals("// KEY_PROOF_STATUS open 3", ProofSaver.marker(false, 3));
    }
}
