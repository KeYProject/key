package org.key_project.slicing;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.Pair;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.stream.Collectors;

public final class ProofSlicer {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofSlicer.class);

    private final Proof proof;
    private final AnalysisResults analysisResults;

    public ProofSlicer(
            Proof proof,
            AnalysisResults analysisResults) {
        if (proof == null || analysisResults == null) {
            throw new NullPointerException();
        }
        this.proof = proof;
        this.analysisResults = analysisResults;
    }

    public Path sliceProof() {
        proof.setStepIndices();
        try {
            var tempFile = Files.createTempFile("", ".proof");
            proof.saveToFile(tempFile.toFile());
            return tempFile;
        } catch (IOException e) {
            LOGGER.error("failed to save temporary proof file", e);
        }
        throw new IllegalStateException("proof slicer failed to save proof");
    }
}
