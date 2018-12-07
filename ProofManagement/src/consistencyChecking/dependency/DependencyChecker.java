package consistencyChecking;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

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
import de.uka.ilkd.key.util.ProgressMonitor;

public class DependencyChecker implements Checker {

    ImmutableList<BranchNodeIntermediate> rootNodes = ImmutableSLList.nil();
    
    final static String PATH = "/home/wolfram/Schreibtisch/Cycle(Cycle__m()).JML operation contract.0.proof";
    
    @Override
    public boolean check(ImmutableList<Path> proofFiles) {
        try {
            // for each proof: construct AST
            for (Path proofPath : proofFiles) {
                rootNodes.prepend(loadFile(proofPath));
            }
            
            buildDependencyGraph();
            
            // TODO: check if dependency graph contains problematic structures,
            //          e.g. cycles, unproven dependencies, ...
            
        } catch (IOException e) {
            // TODO:
        } catch (ProofInputException e) {
            // TODO:
        }
        return true;
    }
    
    private void buildDependencyGraph() {
        // TODO:
    }

    public BranchNodeIntermediate loadFile(Path path) throws IOException, ProofInputException {
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
        BranchNodeIntermediate result = parser.getParsedResult();
        return result;
    }
}
