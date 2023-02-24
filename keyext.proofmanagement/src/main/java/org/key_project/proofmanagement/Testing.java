package org.key_project.proofmanagement;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.key_project.proofmanagement.check.DependencyChecker;

public class Testing {

    static Path proof1 = Paths.get("/home/jakob/Desktop/Problems/Test(Test__m1()).JML operation contract.0.proof");
    static Path proof2 = Paths.get("/home/jakob/Desktop/Problems/Test(Test__m2()).JML operation contract.0.proof");

    public static void main(String[] args) {
        DependencyChecker myDependencyChecker = new DependencyChecker();
        List<Path> proofFiles = new ArrayList<>();
        proofFiles.add(proof1);
        proofFiles.add(proof2);
        //myDependencyChecker.check(proofFiles, );
    }
}
