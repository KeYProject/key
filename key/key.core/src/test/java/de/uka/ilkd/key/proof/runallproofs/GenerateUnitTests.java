package de.uka.ilkd.key.proof.runallproofs;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionSettings;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.TestFile;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * @author Alexander Weigl
 * @version 1 (6/14/20)
 */
public class GenerateUnitTests {
    static String outputFolder;

    static String[] collections = new String[]{
            RunAllProofsFunctional.INDEX_FILE,
            RunAllProofsInfFlow.INDEX_FILE
    };

    public static void main(String[] args) throws IOException {
        if (args.length != 1) {
            System.err.println("Usage: <main> <ouput-folder>");
            System.exit(1);
        }

        outputFolder = args[0];
        log("Output folder %s%n", outputFolder);

        File out = new File(outputFolder);
        out.mkdirs();

        for (String index : collections) {
            log("Index file: %s", index);
            ProofCollection col = RunAllProofsTest.parseIndexFile(index);
            for (RunAllProofsTestUnit unit : col.createRunAllProofsTestUnits()) {
                createUnitClass(col, unit);
            }
        }
    }

    static final String TEMPLATE_CONTENT = "package $packageName;\n" +
            "\n" +
            "import org.junit.*;\n" +
            //"import de.uka.ilkd.key.util.NamedRunner;\n" +
            //"import de.uka.ilkd.key.util.TestName;\n" +
            "import org.junit.rules.Timeout;\n" +
            "import org.junit.runner.RunWith;\n" +
            "\n" +
            //"@org.junit.experimental.categories.Category(org.key_project.util.testcategories.ProofTestCategory.class)\n" +
            //"@RunWith(NamedRunner.class)\n" +
            "public class $className extends de.uka.ilkd.key.proof.runallproofs.ProveTest {\n" +
            "\n" +
            "  @Before public void setUp() {\n" +
            "    this.baseDirectory = \"$baseDirectory\";\n" +
            "    this.statisticsFile = \"$statisticsFile\";\n" +
            "    this.name = \"$name\";\n" +
            "    this.reloadEnabled = $reloadEnabled;\n" +
            "    this.tempDir = \"$tempDir\";\n" +
            "\n" +
            "    this.globalSettings = \"$keySettings\";\n" +
            "    this.localSettings =  \"$localSettings\";\n" +
            "  }\n" +
            "\n" +
            "  $timeout\n" +
            "\n" +
            "  $methods\n" +
            "\n" +
            "}\n";

    private static String readAll(InputStream stream) {
        byte[] buffer = new byte[1024 * 1024];
        try {
            int len = stream.read(buffer);
            return new String(buffer, 0, len, StandardCharsets.UTF_8);
        } catch (IOException e) {
            e.printStackTrace();
        }
        return "";
    }

    private static void createUnitClass(ProofCollection col, RunAllProofsTestUnit unit) throws IOException {
        String packageName = "de.uka.ilkd.key.proof.runallproofs";
        String name = unit.getTestName();
        String className = name
                .replaceAll("\\.java", "")
                .replaceAll("\\.key", "")
                .replaceAll("[^a-zA-Z0-9]+", "_");

        Path tmpDir = unit.getTempDir();
        List<TestFile> files = unit.getTestFiles();
        ProofCollectionSettings settings = unit.getSettings();

        Map<String, String> vars = new TreeMap<>();
        vars.put("className", className);
        vars.put("packageName", packageName);
        vars.put("baseDirectory", settings.getBaseDirectory().getAbsolutePath());
        vars.put("statisticsFile", settings.getStatisticsFile().getStatisticsFile().getAbsolutePath());
        vars.put("name", name);
        vars.put("reloadEnabled", String.valueOf(settings.reloadEnabled()));
        vars.put("tempDir", settings.getTempDir().getAbsolutePath());

        vars.put("globalSettings", settings.getGlobalKeYSettings()
                .replace("\n", "\\n"));
        vars.put("localSettings", (
                settings.getLocalKeYSettings() == null ? "" : settings.getLocalKeYSettings())
                .replace("\n", "\\n"));

        vars.put("timeout", "");

        if (false) {
            int globalTimeout = 0;
            if (globalTimeout > 0)
                vars.put("timeout", "@Rule public Timeout globalTimeout = Timeout.seconds(" + globalTimeout + ");");
        }

        StringBuilder methods = new StringBuilder();
        Set<String> usedMethodNames = new TreeSet<>();
        int clashCounter = 0;

        for (TestFile file : unit.getTestFiles()) {
            File keyFile = file.getKeYFile();
            String testName = keyFile.getName()
                    .replaceAll("\\.java", "")
                    .replaceAll("\\.key", "")
                    .replaceAll("[^a-zA-Z0-9]+", "_");

            if (usedMethodNames.contains(testName)) {
                testName += "_" + (++clashCounter);
            }
            usedMethodNames.add(testName);

            int timeout = 0;// (timeout <= 0 ? parent.timeout : 0)
            String to = timeout > 0 ? "timeout=${1000 * timeout}" : "";
            methods.append("\n");
            methods.append("@Test(").append(to).append(")")
                    //.append("@TestName(\"").append(keyFile.getName()).append("\")")
                    .append("public void test").append(testName).append("() throws Exception {\n");
            //        "// This tests is based on").append(keyFile.getAbsolutePath()).append("\n");

            switch (file.getTestProperty()) {
                case PROVABLE:
                    methods.append("assertProvability(\"").append(keyFile.getAbsolutePath()).append("\");");
                    break;
                case NOTPROVABLE:
                    methods.append("assertUnProvability(\"").append(keyFile.getAbsolutePath()).append("\");");
                    break;
                case LOADABLE:
                    methods.append("assertLoadability(\"").append(keyFile.getAbsolutePath()).append("\");");
                    break;
            }
            methods.append("}");
        }
        vars.put("methods", methods.toString());

        Pattern regex = Pattern.compile("[$](\\w+)");
        Matcher m = regex.matcher(TEMPLATE_CONTENT);
        StringBuffer sb = new StringBuffer();
        while (m.find()) {
            String key = m.group(1);
            m.appendReplacement(sb, vars.getOrDefault(key, "/*not-found*/"));
        }
        m.appendTail(sb);
        File folder = new File(outputFolder, packageName.replace('.', '/'));
        folder.mkdirs();
        Files.write(Paths.get(folder.getAbsolutePath(), className + ".java"), sb.toString().getBytes());
    }

    private static void log(String fmt, Object... args) {
        System.out.printf(">>> " + fmt + "\n", args);
    }
}
