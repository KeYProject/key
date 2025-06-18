package org.key_project.proofmanagement.check;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.speclang.Contract;
import org.jspecify.annotations.Nullable;

import java.net.URL;
import java.nio.file.Path;

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

    /*public Integer settingsId() {
        return choices2Id.get(proof.getSettings().getChoiceSettings().getDefaultChoices());
    }*/
}
