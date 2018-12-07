import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Properties;

import consistencyChecking.dependency.DependencyGraph;
import consistencyChecking.dependency.DependencyNode;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Modality;
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

public class Testing {

	final static String PATH = "/home/jakob/Desktop/Problems/src1/Test(Test__m1()).JML operation contract.0.proof";
	
	public static void main(String[] args) {
		// names
		String name1 = "A";
		String name2 = "B";		
		// modalities
		Modality modality1 = Modality.BOX;
		Modality modality2 = Modality.DIA;
		// nodes
		DependencyNode node1 = new DependencyNode(name1, modality1);
		DependencyNode node2 = new DependencyNode(name2, modality2);
		node1.addDependency(node2);
		node2.addDependency(node1);
		// graph
		DependencyGraph graph = new DependencyGraph();
		graph.addNode(node1);
		graph.addNode(node2);
		
		try {
            loadFile(PATH);
        }
        catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        catch (ProofInputException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
	}
	
	static void loadFile(String path) throws IOException, ProofInputException {
        Profile profile = AbstractProfile.getDefaultProfile();
        FileRepo fileRepo;
        fileRepo = new DiskFileRepo("testProof");
        fileRepo.setBaseDir(Paths.get(path));
        ProgressMonitor control = ProgressMonitor.Empty.getInstance();      
        Path pa = Paths.get(path);
        KeYUserProblemFile keyFile = new KeYUserProblemFile(pa.getFileName().toString(), pa.toFile(), fileRepo,
                control, profile, false);
        
        ProblemInitializer pi = new ProblemInitializer(control, new Services(profile),
                new DefaultUserInterfaceControl());
        pi.setFileRepo(fileRepo);
        InitConfig initConfig = pi.prepare(keyFile);
        initConfig.setFileRepo(fileRepo);
        String proofObligation = keyFile.getProofObligation();
        LoadedPOContainer poContainer;
        final Properties properties = new Properties();
        properties.load(new ByteArrayInputStream(proofObligation.getBytes()));
        properties.setProperty(IPersistablePO.PROPERTY_FILENAME, path);
        poContainer = FunctionalOperationContractPO.loadFrom(initConfig, properties);
        
        ProofAggregate proofList = 
                pi.startProver(initConfig, poContainer.getProofOblInput());

        for (Proof p : proofList.getProofs()) {
            initConfig.getServices().getSpecificationRepository().registerProof(poContainer.getProofOblInput(), p);
        }
        
        Proof proof = proofList.getProof(poContainer.getProofNum());
        IntermediatePresentationProofFileParser parser = null;
        Services srv = new Services(profile);
        parser = new IntermediatePresentationProofFileParser(proof);
        pi.tryReadProof(parser, keyFile);
        BranchNodeIntermediate result = parser.getParsedResult();
        result.toString();
    }
	
}
