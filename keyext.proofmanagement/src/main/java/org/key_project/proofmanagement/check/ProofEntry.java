/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check;

import java.net.URL;
import java.nio.file.Path;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.speclang.Contract;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import static de.uka.ilkd.key.proof.io.IntermediatePresentationProofFileParser.Result;

/**
 * @author Alexander Weigl
 * @version 1 (6/18/25)
 */
public class ProofEntry {
    public CheckerData.LoadingState loadingState = CheckerData.LoadingState.UNKNOWN;
    public CheckerData.ReplayState replayState = CheckerData.ReplayState.UNKNOWN;
    public CheckerData.DependencyState dependencyState = CheckerData.DependencyState.UNKNOWN;
    public CheckerData.ProofState proofState = CheckerData.ProofState.UNKNOWN;

    public boolean replaySuccess() {
        return replayState == CheckerData.ReplayState.SUCCESS;
    }

    public @Nullable Path proofFile;
    public @Nullable KeYUserProblemFile envInput;
    public @Nullable ProblemInitializer problemInitializer;
    public @Nullable Proof proof;

    public @Nullable Contract contract;
    public @Nullable URL sourceFile;
    public @Nullable String shortSrc;
    public @Nullable Result parseResult;
    public @Nullable ReplayResult replayResult;


    public int settingsId(CheckerData data) {
        int val = -1;
        if (proof != null) {
            val = data.getChoices2Id()
                    .getOrDefault(proof.getSettings().getChoiceSettings().getDefaultChoices(), -1);
        }
        return val;
    }


    public @Nullable Contract getContract() {
        return contract;
    }

    public CheckerData.DependencyState getDependencyState() {
        return dependencyState;
    }

    public @Nullable KeYUserProblemFile getEnvInput() {
        return envInput;
    }

    public CheckerData.LoadingState getLoadingState() {
        return loadingState;
    }

    public @Nullable Result getParseResult() {
        return parseResult;
    }

    public @Nullable ProblemInitializer getProblemInitializer() {
        return problemInitializer;
    }

    public @Nullable Proof getProof() {
        return proof;
    }

    public @Nullable Path getProofFile() {
        return proofFile;
    }

    public CheckerData.ProofState getProofState() {
        return proofState;
    }

    public @Nullable ReplayResult getReplayResult() {
        return replayResult;
    }

    public CheckerData.ReplayState getReplayState() {
        return replayState;
    }

    public @Nullable String getShortSrc() {
        return shortSrc;
    }

    public @Nullable URL getSourceFile() {
        return sourceFile;
    }
}
