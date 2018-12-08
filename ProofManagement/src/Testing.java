import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

import consistencyChecking.dependency.DependencyChecker;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.intermediate.BranchNodeIntermediate;

public class Testing {

	static Path PATH = Paths.get("/home/jakob/Desktop/Problems/Test(Test__m1()).JML operation contract.0.proof");
	
	public static void main(String[] args) {
		DependencyChecker myDependencyChecker = new DependencyChecker();
		try {
			BranchNodeIntermediate root =  myDependencyChecker.loadFile(PATH);
			
		} catch (ProofInputException | IOException e) {
			e.printStackTrace();
		}
	}	
}
