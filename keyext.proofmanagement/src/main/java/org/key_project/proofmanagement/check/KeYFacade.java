/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ServiceLoader;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.java.JavaSourceElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.init.loader.ProofObligationLoader;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.IntermediatePresentationProofFileParser;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.io.consistency.TrivialFileRepo;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProgressMonitor;

import org.key_project.proofmanagement.check.dependency.DependencyGraph;
import org.key_project.proofmanagement.check.dependency.DependencyGraphBuilder;
import org.key_project.proofmanagement.io.LogLevel;
import org.key_project.proofmanagement.io.Logger;
import org.key_project.proofmanagement.io.ProofBundleHandler;

/**
 * This class provides static methods to access the prover (KeY).
 *
 * @author Wolfram Pfeifer
 */
public final class KeYFacade {
    // prevents from instantiating this class
    private KeYFacade() {
    }

    /**
     * Ensures that the given CheckerData object has a valid DependencyGraph built.
     * Does not update an existing DependencyGraph!
     *
     * @param data the CheckerData object to store the result
     */
    public static void ensureDependencyGraphBuilt(CheckerData data) {
        if (data.getDependencyGraph() == null) {
            // construct dependency graph from data stored in CheckerData object
            // TODO: the analysis as currently implemented assumes there is
            // exactly one proof for each contract!!!
            DependencyGraph graph = DependencyGraphBuilder.buildGraph(data.getProofEntries(), data);
            data.setDependencyGraph(graph);
        }
    }

    /**
     * Ensures that the given proof files are loaded and the ASTs are stored inside the
     * CheckerData object. Does not replay the proofs! Proofs that already have been loaded
     * are not reloaded.
     *
     * @param data the CheckerData object to store the result
     * @throws ProofManagementException
     */
    public static void ensureProofsLoaded(CheckerData data) throws ProofManagementException {
        List<Path> proofPaths = data.getProofPaths();
        try {
            // for each proof: parse and construct intermediate AST
            Iterator<Path> iterator = proofPaths.iterator();
            // for (Path proofPath : proofPaths) {
            while (iterator.hasNext()) {
                Path proofPath = iterator.next();
                CheckerData.ProofEntry line = ensureProofEntryExists(proofPath, data);
                // only load every line once
                if (line.loadingState == CheckerData.LoadingState.UNKNOWN) {
                    if (!loadProofTree(proofPath, line, data)) {
                        // remove invalid line (e.g. from taclet proof)
                        data.getProofEntries().remove(line);
                        // TODO: code quality (hidden side effect):
                        // modifies given list of paths to check
                        iterator.remove();
                    }
                }
            }
        } catch (Exception e) {
            // TODO: exception handling: better not throw exceptions, but print to log and continue
            throw new ProofManagementException(
                "Could not load proof! " + System.lineSeparator() + e);
        }
    }

    private static CheckerData.ProofEntry ensureProofEntryExists(Path proofPath, CheckerData data) {
        CheckerData.ProofEntry line = findProofLine(proofPath, data);
        if (line == null) {
            line = data.new ProofEntry();
            data.getProofEntries().add(line);
        }
        return line;
    }

    private static CheckerData.ProofEntry findProofLine(Path proofPath, CheckerData data) {
        for (CheckerData.ProofEntry line : data.getProofEntries()) {
            if (line.proofFile != null && line.proofFile.equals(proofPath)) {
                return line;
            }
        }
        return null;
    }

    private static boolean loadProofTree(Path path, CheckerData.ProofEntry line, Logger logger)
            throws Exception {

        logger.print(LogLevel.DEBUG, "Loading proof from " + path);
        line.proofFile = path;
        Proof[] proofs = loadProofFile(path, line);

        // TODO: ignore taclet proofs
        if (proofs == null || proofs.length == 0) {
            logger.print(LogLevel.DEBUG, "Ignoring taclet proof from " + path);
            return false;
        }

        // TODO: what if poContainer contains multiple proofs?
        // Proof proof = proofList.getProof(poContainer.getProofNum());
        Proof proof = proofs[0];
        line.proof = proof;

        // parse the actual proof tree to an intermediate representation (without replay!)
        IntermediatePresentationProofFileParser parser =
            new IntermediatePresentationProofFileParser(proof);
        ProblemInitializer pi = line.problemInitializer;
        KeYUserProblemFile keyFile = line.envInput;
        pi.tryReadProof(parser, keyFile);

        line.parseResult = parser.getResult();

        line.loadingState = CheckerData.LoadingState.SUCCESS;
        logger.print(LogLevel.DEBUG, "... loading done!");
        return true;
    }

    private static Proof[] loadProofFile(Path path, CheckerData.ProofEntry line)
            throws Exception {
        Profile profile = AbstractProfile.getDefaultProfile();

        // TODO: FileRepo/InitConfig/ProblemInitializer reuse possible?
        FileRepo fileRepo = new TrivialFileRepo();
        fileRepo.setBaseDir(path);

        ProgressMonitor control = ProgressMonitor.Empty.getInstance();

        /////////////////// comparison to AbstractProblemLoader load
        /////////////////// createEnvInput
        KeYUserProblemFile keyFile = new KeYUserProblemFile(path.getFileName().toString(),
            path.toFile(), fileRepo, control, profile, false);
        line.envInput = keyFile; // store in CheckerData for later use (e.g. in ReplayChecker)

        /////////////////// createEnvInput
        // TODO: do we need this?
        profile = keyFile.getProfile() == null ? profile : keyFile.getProfile();

        ProblemInitializer pi = new ProblemInitializer(control, new Services(profile),
            new DefaultUserInterfaceControl());
        pi.setFileRepo(fileRepo);
        line.problemInitializer = pi;

        ///////////////////
        InitConfig initConfig = pi.prepare(keyFile);
        initConfig.setFileRepo(fileRepo);

        /////////////////// createProofObligationContainer
        var proofObligation = keyFile.getProofObligation();

        // Load proof obligation settings
        proofObligation.set(IPersistablePO.PROPERTY_FILENAME, path.toString());

        // more generic version (works e.g. for taclet proofs)
        IPersistablePO.LoadedPOContainer poContainer =
            createProofObligationContainer(keyFile, initConfig, proofObligation);

        ProofAggregate proofList = pi.startProver(initConfig, poContainer.getProofOblInput());
        for (Proof p : proofList.getProofs()) {
            // register proof
            initConfig.getServices().getSpecificationRepository()
                    .registerProof(poContainer.getProofOblInput(), p);
            initConfig.getFileRepo().registerProof(p);
        }

        Proof proof = proofList.getFirstProof();
        SpecificationRepository specRepo = initConfig.getServices().getSpecificationRepository();
        ContractPO contractPO = specRepo.getContractPOForProof(proof);
        if (contractPO == null) {
            // happens for taclet proofs (they have no contract)
            // TODO: currently we ignore taclet proofs
            return null;
        }
        Contract contract = contractPO.getContract();
        line.contract = contract;
        Type type = contract.getTarget().getContainerType().getJavaType();
        if (type instanceof JavaSourceElement jse) {
            line.sourceFile = jse.getPositionInfo().getURL().orElseThrow();
            String str = line.sourceFile.toString();
            line.shortSrc = str.substring(str.lastIndexOf('/') + 1);
        }

        return proofList.getProofs();
    }

    // TODO: adapted copy from AbstractProblemLoader

    /**
     * Creates a {@link IPersistablePO.LoadedPOContainer} if available which contains
     * the {@link ProofOblInput} for which a {@link Proof} should be instantiated.
     *
     * @return The {@link IPersistablePO.LoadedPOContainer} or {@code null} if not available.
     * @throws IOException Occurred Exception.
     */
    private static IPersistablePO.LoadedPOContainer createProofObligationContainer(KeYFile keyFile,
            InitConfig initConfig, Configuration properties) throws Exception {
        final String chooseContract = keyFile.chooseContract();
        final Configuration proofObligation = keyFile.getProofObligation();

        // Instantiate proof obligation
        if (keyFile instanceof ProofOblInput && chooseContract == null && proofObligation == null) {
            return new IPersistablePO.LoadedPOContainer((ProofOblInput) keyFile);
        } else if (chooseContract != null && !chooseContract.isEmpty()) {
            int proofNum = 0;
            String baseContractName;
            int ind = -1;
            for (String tag : FunctionalOperationContractPO.TRANSACTION_TAGS.values()) {
                ind = chooseContract.indexOf("." + tag);
                if (ind > 0) {
                    break;
                }
                proofNum++;
            }
            if (ind == -1) {
                baseContractName = chooseContract;
                proofNum = 0;
            } else {
                baseContractName = chooseContract.substring(0, ind);
            }
            final Contract contract = initConfig.getServices()
                    .getSpecificationRepository()
                    .getContractByName(baseContractName);
            if (contract == null) {
                throw new RuntimeException("Contract not found: " + baseContractName);
            } else {
                return new IPersistablePO.LoadedPOContainer(contract.createProofObl(initConfig),
                    proofNum);
            }
        } else if (proofObligation != null) {
            String poClass = properties.getString(IPersistablePO.PROPERTY_CLASS);
            if (poClass == null || poClass.isEmpty()) {
                throw new IOException("Proof obligation class property \""
                    + IPersistablePO.PROPERTY_CLASS + "\" is not defined or empty.");
            }
            ServiceLoader<ProofObligationLoader> loader =
                ServiceLoader.load(ProofObligationLoader.class);
            for (ProofObligationLoader poloader : loader) {
                if (poloader.handles(poClass)) {
                    return poloader.loadFrom(initConfig, proofObligation);
                }
            }
            throw new IllegalArgumentException(
                "There is no builder that can build the PO for the id " + poClass);
        } else {
            return null;
        }
    }

    /**
     * Ensures that a replay is attempted for each proof file in bundle. The replay results are
     * stored
     * inside the given CheckerData object. Proofs for which a replay has already been tried are not
     * replayed again.
     *
     * @param data the CheckerData object to store the result
     * @throws ProofManagementException
     */
    public static void ensureProofsReplayed(CheckerData data) throws ProofManagementException {
        List<Path> proofPaths = data.getProofPaths();
        ensureProofsLoaded(data);

        for (CheckerData.ProofEntry line : data.getProofEntries()) {
            // skip replay for proofs if not requested
            if (proofPaths.contains(line.proofFile)) {
                // skip proofs that have already been replayed
                if (line.replayState == CheckerData.ReplayState.UNKNOWN) {
                    Proof proof = line.proof;
                    EnvInput envInput = line.envInput;

                    if (proof != null) {
                        OneStepSimplifier.refreshOSS(proof);
                        try {
                            // store result in CheckerData
                            line.replayResult = replayProof(line, envInput, data);
                        } catch (ProofInputException e) {
                            throw new ProofManagementException(
                                "Could not replay proof from " + envInput
                                    + System.lineSeparator() + e);
                        }
                    }
                }
            }
        }
    }

    private static ReplayResult replayProof(CheckerData.ProofEntry line, EnvInput envInput,
            Logger logger) throws ProofInputException {
        Proof proof = line.proof;
        logger.print(LogLevel.INFO, "Starting replay of proof " + proof.name());

        List<Throwable> errors = new LinkedList<>();
        Node lastTouchedNode = proof.root();

        IntermediateProofReplayer replayer = null;
        IntermediatePresentationProofFileParser.Result parserResult = null;
        IntermediateProofReplayer.Result replayResult = null;

        final String ossStatus = (String) proof.getSettings()
                .getStrategySettings()
                .getActiveStrategyProperties()
                .get(StrategyProperties.OSS_OPTIONS_KEY);
        ReplayResult result;
        try {
            assert envInput instanceof KeYUserProblemFile;

            // we assume that the proof has been successfully loaded!
            parserResult = line.parseResult;

            // For loading, we generally turn on one step simplification to be
            // able to load proofs that used it even if the user has currently
            // turned OSS off.
            StrategyProperties newProps = proof.getSettings()
                    .getStrategySettings()
                    .getActiveStrategyProperties();
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY,
                StrategyProperties.OSS_ON);
            Strategy.updateStrategySettings(proof, newProps);
            OneStepSimplifier.refreshOSS(proof);

            // passing null is ok since ProblemLoader is only used for error reporting as origin
            replayer = new IntermediateProofReplayer(null, proof, parserResult);
            // pass false here to keep the intermediate tree (may be needed for later checkers)!
            replayResult = replayer.replay(null, null, false);

            Goal lastGoal = replayResult.getLastSelectedGoal();
            lastTouchedNode = lastGoal != null ? lastGoal.node() : proof.root();

        } catch (Exception e) {
            if (parserResult == null || parserResult.errors() == null
                    || parserResult.errors().isEmpty() ||
                    replayer == null || replayResult == null || replayResult.getErrors() == null
                    || replayResult.getErrors().isEmpty()) {
                // this exception was something unexpected
                errors.add(e);
            }
        } finally {
            String status = "";
            if (parserResult != null) {
                status = parserResult.status();
                errors.addAll(parserResult.errors());
            }
            status +=
                (status.isEmpty() ? "" : "\n\n") + (replayResult != null ? replayResult.getStatus()
                        : "Error while loading proof.");
            if (replayResult != null) {
                errors.addAll(replayResult.getErrors());
            }

            // reset OSS
            StrategyProperties newProps = proof.getSettings().getStrategySettings()
                    .getActiveStrategyProperties();
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY, ossStatus);
            Strategy.updateStrategySettings(proof, newProps);
            OneStepSimplifier.refreshOSS(proof);

            result = new ReplayResult(status, errors, lastTouchedNode);
        }

        if (result.hasErrors()) {
            line.replayState = CheckerData.ReplayState.ERROR;
            logger.print(LogLevel.WARNING, result.getErrorList().toString());
            logger.print(LogLevel.WARNING, "... failed!");
        } else {
            line.replayState = CheckerData.ReplayState.SUCCESS;
            // update status from UNKNOWN to OPEN/CLOSED depending on replay result
            if (line.proof.closed()) {
                line.proofState = CheckerData.ProofState.CLOSED;
                logger.print(LogLevel.INFO, "... successful (proof is closed)!");
            } else {
                line.proofState = CheckerData.ProofState.OPEN;
                logger.print(LogLevel.INFO, "... successful (proof is open)!");
            }
        }

        return result;
    }

    /**
     * Ensures that the source files contained by the bundle stored in the given CheckerData object
     * are loaded. Result is stored in CheckerData object as SLEnvInput.
     *
     * @param data the CheckerData object to store the results
     * @throws ProofManagementException
     */
    public static void ensureSourceLoaded(CheckerData data) throws ProofManagementException {
        data.print(LogLevel.DEBUG, "Loading Java sources ...");
        try {
            // load all contracts from source files
            ProofBundleHandler pbh = data.getPbh();
            File src = pbh.getPath("src").toFile();
            List<File> cp = null;
            if (!pbh.getClasspathFiles().isEmpty()) {
                cp = pbh.getClasspathFiles().stream()
                        .map(Path::toFile)
                        .collect(Collectors.toList());
            }
            File bcp = null;
            if (pbh.getBootclasspath() != null) {
                bcp = pbh.getBootclasspath().toFile();
            }

            Profile profile = AbstractProfile.getDefaultProfile();

            SLEnvInput slenv = new SLEnvInput(src.toString(), cp, bcp, profile, null);
            data.setSlenv(slenv);
            data.setSrcLoadingState(CheckerData.LoadingState.SUCCESS);
            data.print(LogLevel.DEBUG, "Java sources successfully loaded!");

        } catch (IOException e) {
            data.setSrcLoadingState(CheckerData.LoadingState.ERROR);
            throw new ProofManagementException("Java sources could not be loaded."
                + System.lineSeparator() + e.getMessage());
        }
    }
}
