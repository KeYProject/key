package proofmanagement;
    // TODO: the checkstyle regex for package name does neither allow proof_management nor proofManagement
    // Is this intended?

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.zip.ZipException;

import proofmanagement.consistencyChecking.DependencyChecker;
import proofmanagement.consistencyChecking.FileConsistencyChecker;
import proofmanagement.consistencyChecking.SettingsChecker;
import proofmanagement.io.PackageHandler;

public class Main {

    /* CLI commands:
     *  check [-s|--settings] [-d|--dependency] [-f|--files] [-r|--report <out_path>] <bundle_path>
     *    options:
     *        -s --settings settings check
     *        -d --dependency dependency check
     *        -f --files files check
     *        -a --auto try to use automode to close open proofs
     *        -e --explicit (implies a) stores automatically found proofs explicitly as files
     *        -r --report generate html report + API
     *    checks that are always enabled:
     *        - check for duplicate proofs of the same contracts
     *        - check for completion state (all POs proven)
     *    individually and independently trigger different checks
     *  merge [-f|--force] [-n|--no-check] <bundle1> <bundle2> ... <output>
     *    options:
     *        -f --force merge the bundles even when the consistency check failed
     *        -n --no-check merge without even performing a check
     */

    private static final String USAGE = "Usage: pm <command>" + System.lineSeparator()
        + System.lineSeparator() + "available commands:" + System.lineSeparator()
        + "    check: Checks a single proof bundle for consistency." + System.lineSeparator()
        + "    merge: Merges two proof bundles." + System.lineSeparator();

    private static final String USAGE_CHECK =
        "pm check [-s|--settings] [-d|--dependency] [-f|--files] [-r|--report <out_path>]" +
            "<bundle_path>" + System.lineSeparator();

    private static final String USAGE_MERGE =
        "pm merge [-f|--force] [-n|--no-check] <bundle1> <bundle2> ... <output>"
            + System.lineSeparator();

    public static void main(String[] args) {
        System.out.println("Proof management is running ...");
        if (args.length != 0) {

            if (args[0].equals("check")) {              // check single bundle for consistency
                if (args.length != 2) {
                    check(args);
                } else {
                    System.out.println(USAGE_CHECK);
                }
            } else if (args[0].equals("merge")) {       // merge at least two bundles
                if (args.length > 2) {
                    merge(args);
                } else {
                    System.out.println(USAGE_MERGE);
                }
            } else {
                System.out.println(USAGE);
            }
        }
    }

    // check [-s|--settings] [-d|--dependency] [-f|--files] [-r|--report <out_path>] <bundle_path>
    private static void check(String[] args) {
        boolean settingsCheck = false;
        boolean dependencyCheck = false;
        boolean filesCheck = false;
        Path reportPath = null;
        Path bundlePath = null;

        for (int i = 1; i < args.length; i++) {         // i == 0 is "check"!
            switch (args[i]) {
            case "-s":
            case "--settings":
                settingsCheck = true;
                break;
            case "-d":
            case "--dependency":
                dependencyCheck = true;
                break;
            case "-f":
            case "--files":
                filesCheck = true;
                break;
            case "-r":
            case "--report":
                if (args.length > i + 1) {
                    reportPath = Paths.get(args[i + 1]);
                    i++; // argument for output -> skip next token
                } else {
                    System.out.println(USAGE_CHECK);
                    return;
                }
                break;
            default:
                if (bundlePath == null) {
                    bundlePath = Paths.get(args[i]);
                } else {
                    System.out.println(USAGE_CHECK);
                    return;
                }
            }
        }

        if (bundlePath == null) {                                           // no bundle given
            System.out.println(USAGE_CHECK);
            return;
        }
        if (!settingsCheck && !dependencyCheck && !filesCheck) {            // no check defined
            System.out.println(USAGE_CHECK);
            return;
        }

        PackageHandler ph = new PackageHandler(bundlePath);
        List<Path> proofFiles = new ArrayList<>();
        try {
            proofFiles.addAll(ph.getProofFiles());
        } catch (ZipException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        if (new SettingsChecker().check(proofFiles).isConsistent()) {
            if (new DependencyChecker().check(proofFiles).isConsistent()) {
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
        List<Path> zproofs = new ArrayList<>();
        zproofs.add(proofA);
        zproofs.add(proofB);
        FileConsistencyChecker.merge(zproofs, newBaseDir);
    }
}
