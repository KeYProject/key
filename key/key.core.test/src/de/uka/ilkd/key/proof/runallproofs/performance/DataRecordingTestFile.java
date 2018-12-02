package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionSettings;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.TestFile;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.TestProperty;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.util.Pair;

@SuppressWarnings("serial")
class DataRecordingTestFile extends TestFile<ProfilingDirectories> {

    public DataRecordingTestFile(TestProperty testProperty, String path, ProofCollectionSettings settings) {
        super(testProperty, path, settings, new ProfilingDirectories(settings.runStart));
    }

    @Override
    protected void autoMode(KeYEnvironment<DefaultUserInterfaceControl> env, Proof loadedProof,
            Pair<String, Location> script) throws Exception {
        // Run KeY prover.
        if (script == null) {
            DataRecordingStrategy strategy = new DataRecordingStrategy(loadedProof, this);
            long begin = System.nanoTime();
            applyStrategy(loadedProof, strategy);
            long end = System.nanoTime();
            strategy.saveCollectedData(end - begin);
        } else {
            // skip executing proof scripts for the time being
        }
    }

    @Override
    protected void reload(boolean verbose, File proofFile, Proof loadedProof, boolean success) {
        // we skip reloading for these test cases
    }
    
    private static ApplyStrategyInfo applyStrategy(Proof proof, Strategy strategy) {
        proof.setActiveStrategy(strategy);
        ApplyStrategyInfo applyStrategyInfo = new ApplyStrategy(proof.getInitConfig().getProfile().getSelectedGoalChooserBuilder().create()).start(proof, proof.openGoals().head());
        return applyStrategyInfo;
    }

}