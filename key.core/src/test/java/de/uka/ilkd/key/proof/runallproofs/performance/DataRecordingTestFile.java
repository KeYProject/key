/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;
import java.io.IOException;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionSettings;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.TestFile;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.TestProperty;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.Strategy;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

class DataRecordingTestFile extends TestFile {
    public final @NonNull ProfilingDirectories directories;

    public DataRecordingTestFile(TestProperty testProperty, String path,
                                 @NonNull ProofCollectionSettings settings) throws IOException {
        super(testProperty, path, settings);
        this.directories = new ProfilingDirectories(settings.runStart);
    }

    @Override
    protected void autoMode(KeYEnvironment<DefaultUserInterfaceControl> env, @NonNull Proof loadedProof,
                            KeyAst.@Nullable ProofScript script) throws Exception {
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

    private static ApplyStrategyInfo applyStrategy(@NonNull Proof proof, @NonNull Strategy strategy) {
        proof.setActiveStrategy(strategy);
        return new ApplyStrategy(
            proof.getInitConfig().getProfile().getSelectedGoalChooserBuilder().create())
                .start(proof, proof.openGoals().head());
    }

    public final @NonNull ProfilingDirectories getProfileDirectories() {
        return directories;
    }
}
