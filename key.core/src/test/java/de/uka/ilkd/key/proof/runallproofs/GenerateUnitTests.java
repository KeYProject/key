/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionSettings;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.TestFile;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Generation of test cases (JUnit) for given proof collection files.
 * <p>
 * This class is intended to be called from gradle. See the gradle task
 * {@code generateRunAllProofs}.
 * <p>
 * The considered proof collections files are configured statically in
 * {@link ProofCollections}.
 *
 * @author Alexander Weigl
 * @version 1 (6/14/20)
 */
public class GenerateUnitTests {
    private static final Logger LOGGER = LoggerFactory.getLogger(GenerateUnitTests.class);
    /**
     * Output folder. Set on command line.
     */
    private static Path outputFolder;

    public static void main(String[] args) throws IOException {
        var collections = List.of(ProofCollections.automaticJavaDL());
        if (args.length != 1) {
            System.err.println("Usage: <main> <output-folder>");
            System.exit(1);
        }
        outputFolder = Paths.get(args[0]);
        run(outputFolder, collections);
    }

    public static void run(Path outputFolder, List<ProofCollection> collections)
            throws IOException {
        LOGGER.info("Output folder {}", outputFolder);

        GenerateUnitTests.outputFolder = outputFolder.toAbsolutePath();
        Files.createDirectories(outputFolder);

        for (var col : collections) {
            for (RunAllProofsTestUnit unit : col.createRunAllProofsTestUnits()) {
                createUnitClass(unit);
            }
        }
    }

    private static final String TEMPLATE_CONTENT =
        """
                /* This file is part of KeY - https://key-project.org
                 * KeY is licensed under the GNU General Public License Version 2
                 * SPDX-License-Identifier: GPL-2.0-only */

                package $packageName;

                import org.junit.jupiter.api.*;
                import static org.junit.jupiter.api.Assertions.*;

                public class $className extends de.uka.ilkd.key.proof.runallproofs.ProveTest {
                  public static final String STATISTIC_FILE = "$statisticsFile";

                  { // initialize during construction
                    this.baseDirectory = "$baseDirectory";
                    this.statisticsFile = STATISTIC_FILE;
                    this.name = "$name";
                    this.reloadEnabled = $reloadEnabled;
                    this.tempDir = "$tempDir";

                    this.globalSettings = "$keySettings";
                    this.localSettings =  "$localSettings";
                  }

                  $timeout
                  $methods
                }
                """;

    /**
     * Generates the test classes for the given proof collection, and writes the
     * java files.
     *
     * @param unit a group of proof collection units
     * @throws IOException if the file is not writable
     */
    private static void createUnitClass(RunAllProofsTestUnit unit)
            throws IOException {
        String packageName = "de.uka.ilkd.key.proof.runallproofs.gen";
        String name = unit.getTestName();
        String className = '_' + name // avoids name clashes, i.e., group "switch"
                .replaceAll("\\.java", "")
                .replaceAll("\\.key", "")
                .replaceAll("[^a-zA-Z0-9]+", "_");

        ProofCollectionSettings settings = unit.getSettings();
        Map<String, String> vars = new TreeMap<>();
        vars.put("className", className);
        vars.put("packageName", packageName);
        vars.put("baseDirectory", settings.getBaseDirectory().getAbsolutePath()
                .replaceAll("\\\\", "/"));
        vars.put("statisticsFile",
            settings.getStatisticsFile().getStatisticsFile().getAbsolutePath()
                    .replaceAll("\\\\", "/"));
        vars.put("name", name);
        vars.put("reloadEnabled", String.valueOf(settings.reloadEnabled()));
        vars.put("tempDir", settings.getTempDir().getAbsolutePath()
                .replaceAll("\\\\", "/"));

        vars.put("globalSettings", settings.getGlobalKeYSettings().replace("\n", "\\n"));
        vars.put("localSettings",
            (settings.getLocalKeYSettings() == null ? "" : settings.getLocalKeYSettings())
                    .replace("\n", "\\n"));

        vars.put("timeout", "");

        if (false) {// disabled
            int globalTimeout = 0;
            if (globalTimeout > 0) {
                vars.put("timeout",
                    "@Rule public Timeout globalTimeout = Timeout.seconds(" + globalTimeout + ");");
            }
        }

        StringBuilder methods = new StringBuilder();
        Set<String> usedMethodNames = new TreeSet<>();
        int clashCounter = 0;

        for (TestFile file : unit.getTestFiles()) {
            Path keyFile = file.getKeYFile();
            String testName = keyFile.getFileName().toString()
                    .replaceAll("\\.java", "")
                    .replaceAll("\\.key", "")
                    .replaceAll("[^a-zA-Z0-9]+", "_");

            if (usedMethodNames.contains(testName)) {
                testName += "_" + (++clashCounter);
            }
            usedMethodNames.add(testName);

            // int timeout = 0; (timeout <= 0 ? parent.timeout : 0)
            String to = ""; // timeout > 0 ? "timeout=${1000 * timeout}" : "";
            methods.append("\n");
            methods.append("@Test(").append(to).append(")")
                    // .append("@TestName(\"").append(keyFile.getName()).append("\")")
                    .append("void test").append(testName).append("() throws Exception {\n");
            // "// This tests is based on").append(keyFile.toAbsolutePath()).append("\n");

            switch (file.getTestProperty()) {
                case PROVABLE -> methods.append("assertProvability(\"")
                        .append(keyFile.toAbsolutePath().toString().replaceAll("\\\\", "/"))
                        .append("\");");
                case NOTPROVABLE -> methods.append("assertUnProvability(\"")
                        .append(keyFile.toAbsolutePath().toString().replaceAll("\\\\", "/"))
                        .append("\");");
                case LOADABLE -> methods.append("assertLoadability(\"")
                        .append(keyFile.toAbsolutePath().toString().replaceAll("\\\\", "/"))
                        .append("\");");
                case NOTLOADABLE -> methods.append("assertUnLoadability(\"")
                        .append(keyFile.toAbsolutePath().toString().replaceAll("\\\\", "/"))
                        .append("\");");
            }
            methods.append("}");
        }
        vars.put("methods", methods.toString());

        Pattern regex = Pattern.compile("[$](\\w+)");
        Matcher m = regex.matcher(TEMPLATE_CONTENT);
        StringBuilder sb = new StringBuilder();
        while (m.find()) {
            String key = m.group(1);
            m.appendReplacement(sb, vars.getOrDefault(key, "/*not-found*/"));
        }
        m.appendTail(sb);
        var folder = outputFolder.resolve(packageName.replace('.', '/'));
        Files.createDirectories(folder);
        Files.writeString(folder.resolve(className + ".java"), sb.toString());
    }
}
