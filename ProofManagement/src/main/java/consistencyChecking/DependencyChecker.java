package consistencyChecking;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.file.Path;
import java.util.Properties;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import consistencyChecking.dependency.DependencyGraph;
import consistencyChecking.dependency.DependencyGraphBuilder;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
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
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.io.IntermediatePresentationProofFileParser;
import de.uka.ilkd.key.proof.io.consistency.DiskFileRepo;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.io.intermediate.BranchNodeIntermediate;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ProgressMonitor;

public class DependencyChecker implements Checker {
    /**
     * The SpecificationRepository which is created when a proof is loaded.
     */
    private SpecificationRepository specRepo = null;

    @Override
    public boolean check(ImmutableList<Path> proofFiles) {
        ImmutableList<Pair<String, BranchNodeIntermediate>> contractProofPairs = ImmutableSLList.nil();
        try {
            // for each proof: construct AST
            for (Path proofPath : proofFiles) {
                Pair<String, BranchNodeIntermediate> currentContractAndProof = loadProof(proofPath);
                contractProofPairs = contractProofPairs.prepend(currentContractAndProof);
            }
            // construct dependency graph from proofs
            // WARNING: the analysis as is currently implemented asserts there is exactly one proof for each contract!!!
        	DependencyGraph dependencyGraph = DependencyGraphBuilder.buildGraph(specRepo, contractProofPairs);
            // check if graph contains illegal structures,
            //			e.g. cycles, unproven dependencies, ...
            if(!dependencyGraph.isLegal()) {
            	// if graph illegal, report problem(s)
            	// TODO: what exactly are the problems
            	//			and how can they be extracted?
            }
        } catch (IOException e) {
            // TODO:
        } catch (ProofInputException e) {
            // TODO:
        }
        return true;
    }

    /**
     * Loads a proof from file without replaying it.
     * @param path the path of the *.proof file.
     * @return a pair of proof name (identifies the contract)
     *          and the root node of the parsed proof tree.
     * @throws IOException
     * @throws ProofInputException
     */
    public Pair<String, BranchNodeIntermediate> loadProof(Path path) throws IOException, ProofInputException {
        Profile profile = AbstractProfile.getDefaultProfile();
        FileRepo fileRepo = new DiskFileRepo("testProof");
        fileRepo.setBaseDir(path);

        ProgressMonitor control = ProgressMonitor.Empty.getInstance();

        KeYUserProblemFile keyFile = new KeYUserProblemFile(path.getFileName().toString(),
                path.toFile(), fileRepo, control, profile, false);

        ProblemInitializer pi = new ProblemInitializer(control, new Services(profile),
                new DefaultUserInterfaceControl());
        pi.setFileRepo(fileRepo);

        InitConfig initConfig = pi.prepare(keyFile);
        initConfig.setFileRepo(fileRepo);

        String proofObligation = keyFile.getProofObligation();

        // Load proof obligation settings
        final Properties properties = new Properties();
        properties.load(new ByteArrayInputStream(proofObligation.getBytes()));
        properties.setProperty(IPersistablePO.PROPERTY_FILENAME, path.toString());

        LoadedPOContainer poContainer = FunctionalOperationContractPO.loadFrom(initConfig, properties);
        ProofAggregate proofList = pi.startProver(initConfig, poContainer.getProofOblInput());

        for (Proof p : proofList.getProofs()) {
            // register proof
            initConfig.getServices().getSpecificationRepository().registerProof(poContainer.getProofOblInput(), p);
        }

        Proof proof = proofList.getProof(poContainer.getProofNum());

        IntermediatePresentationProofFileParser parser = null;

        // set the SpecificationRepo (used in the ContractMap to get the contract from name)
        specRepo = proof.getServices().getSpecificationRepository();

        parser = new IntermediatePresentationProofFileParser(proof);
        pi.tryReadProof(parser, keyFile);

        /* WP: this works with my toy examples, but I don't know how the interplay with
         * ProofAggregates with more than one element is.
         * However, it is safer than reading from the filename. */
        String contractString = proof.name().toString();

        BranchNodeIntermediate proofTree = parser.getParsedResult();
        return new Pair<String, BranchNodeIntermediate>(contractString, proofTree);
    }
}
