package consistencyChecking;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.file.Path;
import java.util.Properties;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import consistencyChecking.dependency.DependencyGraph;
import consistencyChecking.dependency.DependencyGraphFactory;
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
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ProgressMonitor;

public class DependencyChecker implements Checker {

    ImmutableList<Pair<String, BranchNodeIntermediate>> contractProofPairs = ImmutableSLList.nil();
    
    final static String PATH = "/home/wolfram/Schreibtisch/Cycle(Cycle__m()).JML operation contract.0.proof";
    //final static String PATH = "/home/jakob/Desktop/Problems/Test(Test__m1()).JML operation contract.0.proof";
    
    @Override
    public boolean check(ImmutableList<Path> proofFiles) {
        try {
            // for each proof: construct AST
            for (Path proofPath : proofFiles) {
            	Pair<String, BranchNodeIntermediate> currentContractAndProof = loadFile(proofPath);
                contractProofPairs = contractProofPairs.prepend(currentContractAndProof);
            }
            // construct dependency graph from proofs
            DependencyGraphFactory dependencyGraphFactory = new DependencyGraphFactory(contractProofPairs);
        	dependencyGraphFactory.start();
        	DependencyGraph dependencyGraph =  dependencyGraphFactory.getResult();
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

    public Pair<String, BranchNodeIntermediate> loadFile(Path path) throws IOException, ProofInputException {
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
        
        LoadedPOContainer poContainer;
        
        // Load proof obligation settings
        final Properties properties = new Properties();
        properties.load(new ByteArrayInputStream(proofObligation.getBytes()));
        properties.setProperty(IPersistablePO.PROPERTY_FILENAME, path.toString());
        
        poContainer = FunctionalOperationContractPO.loadFrom(initConfig, properties);
        
        ProofAggregate proofList = 
                pi.startProver(initConfig, poContainer.getProofOblInput());

        for (Proof p : proofList.getProofs()) {
            // register proof 
            initConfig.getServices().getSpecificationRepository().registerProof(poContainer.getProofOblInput(), p);
        }
        
        Proof proof = proofList.getProof(poContainer.getProofNum());
        
        IntermediatePresentationProofFileParser parser = null;
        
        parser = new IntermediatePresentationProofFileParser(proof);
        pi.tryReadProof(parser, keyFile);
        // TODO: check if this is really always the proper contract name
        String contractString = path.getFileName().toString();
        BranchNodeIntermediate proofTree = parser.getParsedResult();
        return new Pair<String,BranchNodeIntermediate>(contractString, proofTree);
    }
}
