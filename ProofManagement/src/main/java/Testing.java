import java.nio.file.Path;
import java.nio.file.Paths;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import consistencyChecking.DependencyChecker;

public class Testing {

	static Path proof1 = Paths.get("/home/jakob/Desktop/Problems/Test(Test__m1()).JML operation contract.0.proof");
	static Path proof2 = Paths.get("/home/jakob/Desktop/Problems/Test(Test__m2()).JML operation contract.0.proof");
	
	public static void main(String[] args) {
		DependencyChecker myDependencyChecker = new DependencyChecker();
		ImmutableList<Path> proofFiles = ImmutableSLList.nil();
		proofFiles = proofFiles.prepend(proof1);
		proofFiles = proofFiles.prepend(proof2);
		myDependencyChecker.check(proofFiles);
	}	
}
