/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.IOException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.TacletForTests;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class ProofSaverTest {

    void testSaveProblemToFile(String content) throws IOException {
        Services services = TacletForTests.services();
        KeyIO io = new KeyIO(services);
        KeyIO.Loader loader = io.load(content);
        Sequent seq = loader.parseFile().loadProblem().getProblem();
        final InitConfig initConfig =
            new InitConfig(new Services(AbstractProfile.getDefaultProfile()));
        Proof proof = new Proof("test", seq, "", initConfig, null);
        File file = File.createTempFile("proofSaveTest", ".key");
        file.deleteOnExit();
        String status = new ProofSaver(proof, file).save();
        assertNull(status);

        KeyIO io2 = new KeyIO(services);
        KeyIO.Loader loader2 = io2.load(content);
        Sequent seq2 = loader2.parseFile().loadProblem().getProblem();

        assertEquals(seq, seq2);
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
}
