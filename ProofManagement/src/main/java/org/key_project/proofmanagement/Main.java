package org.key_project.proofmanagement;
    // TODO: the checkstyle regex for package name does neither allow proof_management nor proofManagement
    // Is this intended?

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.zip.ZipException;

import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;
import org.key_project.proofmanagement.check.DependencyChecker;
import org.key_project.proofmanagement.check.FileConsistencyChecker;
import org.key_project.proofmanagement.check.SettingsChecker;
import org.key_project.proofmanagement.io.PackageHandler;

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

    private static CommandLine setUpCL() {
        CommandLine cl = new CommandLine();
        cl.addSubCommand("check");
        CommandLine check = cl.getSubCommandLine("check");
        check.addOption("--settings", null, "Enables check for consistent proof settings");
        check.addOption("--dependency", null, "Enables check for cyclic dependencies");
        check.addOption("--files", null, "Enables check for compatible files");
        check.addOption("--report", "out_path", "Writes the report to a HTML file at the given path");

        cl.addSubCommand("merge");
        CommandLine merge = cl.getSubCommandLine("merge");
        return cl;
    }

    public static void main(String[] args) {
        System.out.println("Proof management is running ...");

        try {
            CommandLine cl = setUpCL();
            cl.parse(args);
            if (cl.subCommandUsed("check")) {
                check(cl.getSubCommandLine("check"));
            } else if (cl.subCommandUsed("merge")) {
                merge(cl.getSubCommandLine("merge"));
            }
        } catch (CommandLineException e) {
            e.printStackTrace();
        }
    }

    // check [-s|--settings] [-d|--dependency] [-f|--files] [-r|--report <out_path>] <bundle_path>
    private static void check(CommandLine commandLine) {

        List<String> arguments = commandLine.getArguments();
        if (arguments.size() != 1) {
            System.out.println("Error! Single file needed: <bundle_path>");
        }

        Path bundlePath = Paths.get(arguments.get(0));
        PackageHandler ph = new PackageHandler(bundlePath);

        List<Path> proofFiles = new ArrayList<>();
        try {
            for (String s : arguments) {
                proofFiles.addAll(ph.getProofFiles());
            }
        } catch (ZipException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }

        if (commandLine.isSet("--settings")) {
            if (new SettingsChecker().check(proofFiles).isConsistent()) {
                System.out.println("    Consistent! Settings consistent!");
            } else {
                System.out.println("    Inconsistent! Settings do not match!");
            }
        }
        if (commandLine.isSet("--dependency")) {
            if (new DependencyChecker().check(proofFiles).isConsistent()) {
                System.out.println("    Consistent! No cycles found!");
            } else {
                System.out.println("    Inconsistent! Cyclic dependency found!");
            }
        }
        if (commandLine.isSet("--files")) {
            if (new FileConsistencyChecker().check(List.of(bundlePath)).isConsistent()) {
                System.out.println("    Consistent! Files consistent!");
            } else {
                System.out.println("    Inconsistent! Different files found in bundles!");
            }
        }
        if (commandLine.isSet("--report")) {

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

    private static void merge(CommandLine commandLine) {
        if (commandLine.isSet("--force")) {

        }
        // ...
        // TODO
    }
}
