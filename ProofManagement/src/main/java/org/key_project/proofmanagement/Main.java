package org.key_project.proofmanagement;
    // TODO: the checkstyle regex for package name does neither allow proof_management nor proofManagement
    // Is this intended?

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.zip.ZipException;

import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;
import org.key_project.proofmanagement.check.CheckResult;
import org.key_project.proofmanagement.check.DependencyChecker;
import org.key_project.proofmanagement.merge.FilesChecker;
import org.key_project.proofmanagement.check.SettingsChecker;
import org.key_project.proofmanagement.io.PackageHandler;
import org.key_project.proofmanagement.io.report.Report;
import org.key_project.proofmanagement.merge.ProofBundleMerger;

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
        merge.addOption("--force", null, "Tries to merge the proof bundles even if the files check fails (may rename some files). Only use if you know what you are doing!");
        merge.addOption("--check", "check_arguments", "Performs a check after successful merge. The arguments are passed too check");

        // enable check option forwarding for merge command
        merge.addSubCommand("check");
        CommandLine merge_check = merge.getSubCommandLine("check");
        merge_check.addOption("--settings", null, "Enables check for consistent proof settings");
        merge_check.addOption("--dependency", null, "Enables check for cyclic dependencies");
        merge_check.addOption("--files", null, "Enables check for compatible files");
        merge_check.addOption("--report", "out_path", "Writes the report to a HTML file at the given path");

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
            //for (String s : arguments) {
                proofFiles.addAll(ph.getProofFiles());
            //}
        } catch (ZipException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }

        // we accumulate results in this variable
        CheckResult globalResult = new CheckResult(true);

        if (commandLine.isSet("--settings")) {
            CheckResult result = new SettingsChecker().check(proofFiles);
            globalResult.join(result);
            if (result.isConsistent()) {
                System.out.println("    Consistent! Settings consistent!");
            } else {
                System.out.println("    Inconsistent! Settings do not match!");
            }
        }
        if (commandLine.isSet("--dependency")) {
            CheckResult result = new DependencyChecker().check(proofFiles);
            globalResult.join(result);
            if (result.isConsistent()) {
                System.out.println("    Consistent! No cycles found!");
            } else {
                System.out.println("    Inconsistent! Cyclic dependency found!");
            }
        }
        // TODO: it is not clear what a file checker could do for only a single bundle ...
        /*
        if (commandLine.isSet("--files")) {
            List<Path> list = new ArrayList<>();
            list.add(bundlePath);
            CheckResult result = new FilesChecker().check(list);
            globalResult.join(result);
            if (result.isConsistent()) {
                System.out.println("    Consistent! Files consistent!");
            } else {
                System.out.println("    Inconsistent! Different files found in bundles!");
            }
        }
        */
        if (commandLine.isSet("--report")) {
            String outFileName = commandLine.getString("--report", "");
            Path output = Paths.get(outFileName).toAbsolutePath();
            Report report = new Report(globalResult);
            report.setOutPath(output);
            try {
                System.out.println(report.printReport());
            } catch (IOException e) {
                e.printStackTrace();
            } catch (URISyntaxException e) {
                e.printStackTrace();
            }
        }
    }

    // merge [-f|--force] [-n|--no-check] [--check "<check_args>"] <bundle1> <bundle2> ... <output>
    private static void merge(CommandLine commandLine) {
        List<String> arguments = commandLine.getArguments();

        // at least three files!
        if (arguments.size() < 3) {
            System.out.println("Error! Specify at least two input files and one output file:");
            System.out.println(USAGE_MERGE);
        }

        // convert Strings to Paths (for input and output)
        List<Path> inputs = new ArrayList<>();
        for (int i = 0; i < arguments.size() - 1; i++) {
            inputs.add(Paths.get(arguments.get(i)));
        }
        Path output = Paths.get(arguments.get(arguments.size() - 1));

        if (commandLine.isSet("--force")) {
            // TODO:
        }

        // TODO: use result, print message, clean up particularly created zips
        ProofBundleMerger.merge(inputs, output);

        // perform a check with given commands
        if (commandLine.isSet("--check")) {
            String[] temp = commandLine.getString("--check", "").trim().split(" ");
            String[] newArgs = Arrays.copyOfRange(temp, 0,temp.length + 1);
            newArgs[newArgs.length - 1] = output.toString();
            try {
                CommandLine checkCommandLine = commandLine.getSubCommandLine("check");
                checkCommandLine.parse(newArgs);
                check(checkCommandLine);
            } catch (CommandLineException e) {
                e.printStackTrace();
            }
        }

    }
}
