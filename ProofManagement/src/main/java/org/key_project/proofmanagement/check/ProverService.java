package org.key_project.proofmanagement.check;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.java.JavaSourceElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.IntermediatePresentationProofFileParser;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.io.consistency.TrivialFileRepo;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProgressMonitor;
import org.key_project.proofmanagement.check.dependency.DependencyGraph;
import org.key_project.proofmanagement.check.dependency.DependencyGraphBuilder;
import org.key_project.proofmanagement.io.ProofBundleHandler;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;
import java.util.stream.Collectors;

/**
 * This class provides static methods to access the prover (KeY).
 *
 * @author Wolfram Pfeifer
 */
public final class ProverService {
    // prevents from instantiating this class
    private ProverService() {
    }

    /**
     * Ensures that the given CheckerData object has a valid DependencyGraph built.
     * Does not update an existing DependencyContract!
     * @param data the CheckerData object to store the result
     */
    public static void ensureDependencyGraphBuilt(CheckerData data) {
        if (data.getDependencyGraph() == null) {
            // construct dependency graph from data stored in CheckerData object
            // TODO: the analysis as currently implemented assumes there is
            //  exactly one proof for each contract!!!
            DependencyGraph graph = DependencyGraphBuilder.buildGraph(data.getProofEntries(), data);
            data.setDependencyGraph(graph);
        }
    }

    /**
     * Ensures that the given proof files are loaded and the ASTs are stored inside the
     * CheckerData object. Does not replay the proofs! Proofs that already have been loaded
     * are not reloaded.
     * @param proofPaths the list of proofs to load
     * @param data the CheckerData object to store the result
     * @throws ProofManagementException
     */
    public static void ensureProofsLoaded(List<Path> proofPaths, CheckerData data) throws ProofManagementException {
        try {
            // for each proof: parse and construct intermediate AST
            for (Path proofPath : proofPaths) {
                CheckerData.ProofEntry line = ensureProofEntryExists(proofPath, data);
                loadProofTree(proofPath, line);
            }
        } catch (IOException | ProofInputException e) {
            throw new ProofManagementException("Could not load proof! " + System.lineSeparator() + e.toString());
        }
    }

    private static CheckerData.ProofEntry ensureProofEntryExists(Path proofPath, CheckerData data) {
        CheckerData.ProofEntry line = findProofLine(proofPath, data);
        if (line == null) {
            line = new CheckerData.ProofEntry();
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

    private static void loadProofTree(Path path, CheckerData.ProofEntry line) throws ProofInputException, IOException {

        line.proofFile = path;
        Proof[] proofs = loadProofFile(path, line);

        // TODO: what if poContainer contains multiple proofs?
        //Proof proof = proofList.getProof(poContainer.getProofNum());
        Proof proof = proofs[0];
        line.proof = proof;

        // parse the actual proof tree to an intermediate representation (without replay!)
        IntermediatePresentationProofFileParser parser = new IntermediatePresentationProofFileParser(proof);
        ProblemInitializer pi = line.problemInitializer;
        KeYUserProblemFile keyFile = line.envInput;
        pi.tryReadProof(parser, keyFile);

        line.rootNode = parser.getParsedResult();
    }

    private static Proof[] loadProofFile(Path path, CheckerData.ProofEntry line) throws ProofInputException, IOException {
        Profile profile = AbstractProfile.getDefaultProfile();

        // TODO: FileRepo/InitConfig/ProblemInitializer reuse possible?
        FileRepo fileRepo = new TrivialFileRepo();
        fileRepo.setBaseDir(path);

        ProgressMonitor control = ProgressMonitor.Empty.getInstance();

        KeYUserProblemFile keyFile = new KeYUserProblemFile(path.getFileName().toString(),
                path.toFile(), fileRepo, control, profile, false);
        line.envInput = keyFile;    // store in CheckerData for later use (e.g. in ReplayChecker)

        ProblemInitializer pi = new ProblemInitializer(control, new Services(profile),
                new DefaultUserInterfaceControl());
        pi.setFileRepo(fileRepo);
        line.problemInitializer = pi;

        InitConfig initConfig = pi.prepare(keyFile);
        initConfig.setFileRepo(fileRepo);

        String proofObligation = keyFile.getProofObligation();

        // Load proof obligation settings
        final Properties properties = new Properties();
        properties.load(new ByteArrayInputStream(proofObligation.getBytes()));
        properties.setProperty(IPersistablePO.PROPERTY_FILENAME, path.toString());

        IPersistablePO.LoadedPOContainer poContainer = FunctionalOperationContractPO.loadFrom(initConfig, properties);

        ProofAggregate proofList = pi.startProver(initConfig, poContainer.getProofOblInput());
        for (Proof p : proofList.getProofs()) {
            // register proof
            initConfig.getServices().getSpecificationRepository()
                    .registerProof(poContainer.getProofOblInput(), p);
            initConfig.getFileRepo().registerProof(p);
        }

        Proof proof = proofList.getFirstProof();
        SpecificationRepository specRepo = initConfig.getServices().getSpecificationRepository();
        Contract contract = specRepo.getContractPOForProof(proof).getContract();
        line.contract = contract;
        Type type = contract.getTarget().getContainerType().getJavaType();
        if (type instanceof JavaSourceElement) {
            JavaSourceElement jse = (JavaSourceElement) type;
            line.sourceFile = jse.getPositionInfo().getURI().toURL();
            String str = line.sourceFile.toString();
            line.shortSrc = str.substring(str.lastIndexOf('/') + 1);
        }

        return proofList.getProofs();
    }

    /**
     * Ensures that the given proof files are loaded and the parsed proof trees are stored inside
     * the CheckerData object. Does not replay the proofs! Proofs that already have been loaded
     * are not reloaded.
     * @param proofPaths paths of the proof files to load
     * @param data the CheckerData object to store the result
     * @throws ProofManagementException
     */
    public static void ensureProofsReplayed(List<Path> proofPaths, CheckerData data) throws ProofManagementException {
        ensureProofsLoaded(proofPaths, data);

        for (CheckerData.ProofEntry line : data.getProofEntries()) {
            // skip replay for proofs if not requested
            if (proofPaths.contains(line.proofFile)) {
                Proof proof = line.proof;
                EnvInput envInput = line.envInput;
                ProblemInitializer problemInitializer = line.problemInitializer;

                if (proof != null) {
                    OneStepSimplifier.refreshOSS(proof);
                    try {
                        // store result in CheckerData
                        line.replayResult = replayProof(proof, envInput, problemInitializer);
                    } catch (ProofInputException e) {
                        throw new ProofManagementException("Could not replay proof from " + envInput
                                + System.lineSeparator() + e.toString());
                    }
                }
            }
        }
    }

    private static AbstractProblemLoader.ReplayResult replayProof(Proof proof, EnvInput envInput, ProblemInitializer problemInitializer) throws ProofInputException {
        String status = "";
        List<Throwable> errors = new LinkedList<>();
        Node lastTouchedNode = proof.root();

        IntermediatePresentationProofFileParser parser = null;
        IntermediateProofReplayer replayer = null;
        IntermediatePresentationProofFileParser.Result parserResult = null;
        IntermediateProofReplayer.Result replayResult = null;

        final String ossStatus = (String) proof.getSettings().getStrategySettings()
                                               .getActiveStrategyProperties()
                                               .get(StrategyProperties.OSS_OPTIONS_KEY);
        AbstractProblemLoader.ReplayResult result;
        try {
            assert envInput instanceof KeYUserProblemFile;

            parser = new IntermediatePresentationProofFileParser(proof);
            problemInitializer.tryReadProof(parser, (KeYUserProblemFile) envInput);
            parserResult = parser.getResult();

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

            // passing null is ok since ProblemLoader is only used for error reporting as origin
            replayer = new IntermediateProofReplayer(null, proof, parserResult);
            replayResult = replayer.replay();

            Goal lastGoal = replayResult.getLastSelectedGoal();
            lastTouchedNode = lastGoal != null ? lastGoal.node() : proof.root();

        /*} catch (Exception e) {
            if (parserResult == null || parserResult.getErrors() == null || parserResult.getErrors().isEmpty() ||
                replayer == null || replayResult == null || replayResult.getErrors() == null || replayResult.getErrors().isEmpty()) {
                // this exception was something unexpected
                errors.add(e);
            }*/
        } finally {
            if (parserResult != null) {
                status = parserResult.getStatus();
                errors.addAll(parserResult.getErrors());
            }
            status += (status.isEmpty() ? "" : "\n\n") + (replayResult != null ? replayResult.getStatus() : "Error while loading proof.");
            if (replayResult != null) {
                errors.addAll(replayResult.getErrors());
            }

            StrategyProperties newProps = proof.getSettings().getStrategySettings()
                    .getActiveStrategyProperties();
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY, ossStatus);
            Strategy.updateStrategySettings(proof, newProps);
            OneStepSimplifier.refreshOSS(proof);

            result = new AbstractProblemLoader.ReplayResult(status, errors, lastTouchedNode);
        }

        return result;
    }

    /**
     * Ensures that the source files contained by the bundle stored in the given CheckerData object
     * are loaded. Result is stored in CheckerData object as SLEnvInput.
     * @param data the CheckerData object to store the results
     * @throws ProofManagementException
     */
    public static void ensureSourceLoaded(CheckerData data) throws ProofManagementException {
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
            if (!pbh.getBootclasspathFiles().isEmpty()) {
                bcp = pbh.getPath("bcp").toFile();
            }

            Profile profile = AbstractProfile.getDefaultProfile();

            SLEnvInput slenv = new SLEnvInput(src.toString(), cp, bcp, profile, null);
            data.setSlenv(slenv);

//            ProgressMonitor control = ProgressMonitor.Empty.getInstance();
//            ProblemInitializer pi = new ProblemInitializer(control, new Services(profile),
//                    new DefaultUserInterfaceControl());
//            pi.setFileRepo(new TrivialFileRepo());
//            InitConfig ic = pi.prepare(slenv);
//            SpecificationRepository specRepo = ic.getServices().getSpecificationRepository();
//            Set<Contract> contracts = specRepo.getAllContracts().toSet();
//        } catch (ProofInputException e) {
//            throw new ProofManagementException("Java source could not be loaded."
//                + System.lineSeparator() + e.getMessage());
        } catch (IOException e) {
            throw new ProofManagementException(System.lineSeparator() + e.getMessage());
        }
    }
}
