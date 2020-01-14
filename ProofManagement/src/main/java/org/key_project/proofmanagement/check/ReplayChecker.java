package org.key_project.proofmanagement.check;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.*;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;

import java.nio.file.Path;
import java.util.LinkedList;
import java.util.List;

/**
 * Checks that all files stored in the bundle can successfully be replayed.
 */
public class ReplayChecker implements Checker {

    @Override
    public CheckerData check(List<Path> proofFiles, CheckerData currentRes) {

        // TODO: iterate
        Proof proof = currentRes.getProofLines().get(0).proof;
        EnvInput envInput = currentRes.getProofLines().get(0).envInput;
        ProblemInitializer problemInitializer = currentRes.getProofLines().get(0).problemInitializer;

        AbstractProblemLoader.ReplayResult result;

        if (proof != null) {
            OneStepSimplifier.refreshOSS(proof);
            try {
                result = replayProof(proof, envInput, problemInitializer);
                // TODO: store result in CheckerData
            } catch (ProofInputException e) {
                e.printStackTrace();
            } catch (ProblemLoaderException e) {
                e.printStackTrace();
            }
        }

        return null;
    }

    private AbstractProblemLoader.ReplayResult replayProof(Proof proof, EnvInput envInput, ProblemInitializer problemInitializer) throws ProofInputException, ProblemLoaderException {
        String status = "";
        List<Throwable> errors = new LinkedList<>();
        Node lastTouchedNode = proof.root();

        IProofFileParser parser = null;
        IntermediateProofReplayer replayer = null;
        IntermediatePresentationProofFileParser.Result parserResult = null;
        IntermediateProofReplayer.Result replayResult = null;

        final String ossStatus =
            (String) proof.getSettings().getStrategySettings()
                .getActiveStrategyProperties()
                .get(StrategyProperties.OSS_OPTIONS_KEY);
        AbstractProblemLoader.ReplayResult result;
        try {
            assert envInput instanceof KeYUserProblemFile;

            parser = new IntermediatePresentationProofFileParser(proof);
            problemInitializer.tryReadProof(parser, (KeYUserProblemFile) envInput);
            parserResult = ((IntermediatePresentationProofFileParser) parser).getResult();

            // Parser is no longer needed, set it to null to free memory.
            parser = null;

            // For loading, we generally turn on one step simplification to be
            // able to load proofs that used it even if the user has currently
            // turned OSS off.
            StrategyProperties newProps = proof.getSettings()
                .getStrategySettings().getActiveStrategyProperties();
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY,
                StrategyProperties.OSS_ON);
            Strategy.updateStrategySettings(proof, newProps);
            OneStepSimplifier.refreshOSS(proof);

            // TODO: passing null may be ok since the ProblemLoader is only used in error reporting
            //  as origin
            replayer = new IntermediateProofReplayer(null, proof, parserResult);
            replayResult = replayer.replay();

            lastTouchedNode = replayResult.getLastSelectedGoal() != null ? replayResult.getLastSelectedGoal().node() : proof.root();

        } catch (Exception e) {
            if (parserResult == null || parserResult.getErrors() == null || parserResult.getErrors().isEmpty() ||
                replayer == null || replayResult == null || replayResult.getErrors() == null || replayResult.getErrors().isEmpty()) {
                // this exception was something unexpected
                errors.add(e);
            }
        } finally {
            if (parserResult != null) {
                status = parserResult.getStatus();
                errors.addAll(parserResult.getErrors());
            }
            status += (status.isEmpty() ? "" : "\n\n") + (replayResult != null ? replayResult.getStatus() : "Error while loading proof.");
            if (replayResult != null) {
                errors.addAll(replayResult.getErrors());
            }

            StrategyProperties newProps =
                proof.getSettings().getStrategySettings()
                    .getActiveStrategyProperties();
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY,
                ossStatus);
            Strategy.updateStrategySettings(proof, newProps);
            OneStepSimplifier.refreshOSS(proof);

            result = new AbstractProblemLoader.ReplayResult(status, errors, lastTouchedNode);
        }

        return result;
    }
}
