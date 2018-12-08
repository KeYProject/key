import java.nio.file.Path;
import java.nio.file.Paths;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import consistencyChecking.DependencyChecker;

public class Testing {

	static Path PATH = Paths.get("/home/jakob/Desktop/Problems/Test(Test__m1()).JML operation contract.0.proof");
	
	public static void main(String[] args) {
		DependencyChecker myDependencyChecker = new DependencyChecker();
		ImmutableList<Path> proofFiles = ImmutableSLList.nil();
		proofFiles = proofFiles.prepend(PATH);
		myDependencyChecker.check(proofFiles);
	}	
}
