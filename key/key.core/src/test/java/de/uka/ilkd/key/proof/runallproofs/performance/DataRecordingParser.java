package de.uka.ilkd.key.proof.runallproofs.performance;

import org.antlr.runtime.TokenStream;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionParser;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionSettings;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.TestProperty;

public class DataRecordingParser extends ProofCollectionParser {

    public DataRecordingParser(TokenStream input) {
        super(input);
    }

    @Override
    public DataRecordingTestFile getTestFile(TestProperty testProperty, String path, ProofCollectionSettings settings) {
        return new DataRecordingTestFile(testProperty, path, settings);
    }
}