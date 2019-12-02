package proofmanagement;
    // TODO: the checkstyle regex for package name does neither allow proof_management nor proofManagement
    // Is this intended?

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.zip.ZipException;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import proofmanagement.consistencyChecking.DependencyChecker;
import proofmanagement.consistencyChecking.FileConsistencyChecker;
import proofmanagement.consistencyChecking.SettingsChecker;
import proofmanagement.io.PackageHandler;

public class Main {

    /* different modes:
     *  - check
     *      options:
     *          -s settings check
     *          -d dependency check
     *          -f files check
     *          -o generate html report + API
     *      individually and independently trigger different checks
     *  - merge
     *      force
     *
     *
     *
     *
     */

    private static final String USAGE = "Usage: TODO";

    public static void main(String[] args) {
        System.out.println("Proof management is running ...");
        if (args.length != 0) {

            // check single bundle for consistency
            if (args[0].equals("check") && (args.length == 2)) {
                check(args);
            } else if (args[0].equals("merge") && args.length > 2) {  // merge at least two bundles
                merge(args);
            } else {
                System.out.println(USAGE);
            }
        }
    }

    private static void check(String[] args) {
        PackageHandler ph = new PackageHandler(Paths.get(args[1]));
        ImmutableList<Path> proofFiles = ImmutableSLList.nil();
        try {
            proofFiles = proofFiles.append(ph.getProofFiles());
        } catch (ZipException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        if (new SettingsChecker().check(proofFiles)) {
            if (new DependencyChecker().check(proofFiles)) {
                System.out.println("Consistent! Settings consistent and no cycles found!");
            } else {
                System.out.println("Inconsistent! Cyclic dependencies detected!");
            }
        } else {
            // TODO: print more information
            System.out.println("Inconsistent! Settings do not match!");
        }
    }

    private static void merge(String[] args) {
        Path newBaseDir = Paths.get("/home/jonas/tmp/hackeython/testtest/");
        Path proofA = Paths.get("/home/jonas/tmp/hackeython/proof42.zip");
        Path proofB = Paths.get("/home/jonas/tmp/hackeython/proof43.zip");
        ImmutableList<Path> zproofs = ImmutableSLList.nil();
        zproofs = zproofs.append(proofA, proofB);
        FileConsistencyChecker.merge(zproofs, newBaseDir);
    }
}
