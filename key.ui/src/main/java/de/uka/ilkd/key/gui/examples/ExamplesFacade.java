package de.uka.ilkd.key.gui.examples;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
import org.key_project.util.java.IOUtil;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;

/// @author Alexander Weigl
/// @version 1 (4/4/26)
public class ExamplesFacade {
    private static final Logger LOGGER = LoggerFactory.getLogger(ExamplesFacade.class);

    /// This path is also accessed by the Eclipse integration of KeY to find the right examples.
    public static final String EXAMPLES_PATH = "examples";

    /// This constant is accessed by the eclipse based projects.
    public static final String KEY_FILE_NAME = "project.key";

    static final String PROOF_FILE_NAME = "project.proof";

    /// Java property name to specify a custom key example folder.
    public static final String KEY_EXAMPLE_DIR = "key.examples.dir";

    /**
     * The default category under which examples range if they do not have {@link #KEY_PATH}
     * set.
     */
    private static final String DEFAULT_CATEGORY_PATH = "Unsorted";

    /**
     * The {@link Properties} key to specify the path in the tree.
     */
    private static final String KEY_PATH = "example.path";

    /**
     * The {@link Properties} key to specify the name of the example. Directory name if left
     * open.
     */
    private static final String KEY_NAME = "example.name";

    /**
     * The {@link Properties} key to specify the file for the example. KEY_FILE_NAME by default
     */
    private static final String KEY_FILE = "example.file";

    /**
     * The {@link Properties} key to specify the proof file in the tree. May be left open
     */
    private static final String KEY_PROOF_FILE = "example.proofFile";

    /**
     * The {@link Properties} key to specify the path in the tree. Prefix to specify additional
     * files to load. Append 1, 2, 3, ...
     */
    private static final String ADDITIONAL_FILE_PREFIX = "example.additionalFile.";

    /**
     * The {@link Properties} key to specify the path in the tree. Prefix to specify export
     * files which are not shown as tabs in the example wizard but are extracted to Java
     * projects in the Eclipse integration. Append 1, 2, 3, ...
     */
    private static final String EXPORT_FILE_PREFIX = "example.exportFile.";


    /// @return a File object pointing to the folder of the examples
    public static File lookForExamples() {
        // weigl: using java properties: -Dkey.examples.dir="..."
        final var alternativeDirectory = System.getProperty(KEY_EXAMPLE_DIR);
        if (alternativeDirectory != null) {
            LOGGER.info("Using {} to load the examples directory.", alternativeDirectory);
            return new File(alternativeDirectory);
        }

        // greatly simplified version without parent path lookup.
        File folder = new File(IOUtil.getProjectRoot(ExampleChooser.class), EXAMPLES_PATH);
        if (!folder.exists()) {
            folder = new File(IOUtil.getClassLocation(ExampleChooser.class), EXAMPLES_PATH);
        }
        return folder;
    }

    static String fileAsString(Path f) {
        try {
            return Files.readString(f);
        } catch (IOException e) {
            LOGGER.error("Could not read file '{}'", f, e);
            return "<Error reading file: " + f + ">";
        }
    }

    public static Example loadExample(Path file) throws IOException {
        final var fileName = file.getFileName().toString();
        if (fileName.endsWith(".txt")) {
            return loadExampleLegacy(file);
        }

        if (fileName.endsWith(".json")) {
            return loadExampleJson(file);
        }

        throw new IllegalArgumentException("Unsupported file type: " + file);
    }

    private static Example loadExampleJson(Path file) {
        return new Example();
    }

    private static Example loadExampleYml(Path file) throws IOException {
        var om = new ObjectMapper(new YAMLFactory());
        return om.readValue(file.toFile(), Example.class);
    }

    public static Example loadExampleLegacy(Path file) {
        var directory = file.getParent();
        var properties = new Properties();
        StringBuilder sb = new StringBuilder();
        ExamplesFacade.extractDescription(file, sb, properties);
        var description = sb.toString();


        var proofFile = directory.resolve(properties.getProperty(KEY_PROOF_FILE, PROOF_FILE_NAME));
        var obligationFile = directory.resolve(properties.getProperty(KEY_FILE, KEY_FILE_NAME));
        var name = properties.getProperty(KEY_NAME, directory.getFileName().toString());

        ArrayList<Path> additionalFiles = new ArrayList<>();
        int i = 1;
        while (properties.containsKey(ADDITIONAL_FILE_PREFIX + i)) {
            additionalFiles.add(directory.resolve(properties.getProperty(ADDITIONAL_FILE_PREFIX + i)));
            i++;
        }
        List<String> path = Arrays.stream(properties.getProperty(KEY_PATH, DEFAULT_CATEGORY_PATH).split("/"))
                .toList();
        return new Example(
                name, path, directory, description, obligationFile, proofFile, additionalFiles);
    }


    static StringBuilder extractDescription(Path file, StringBuilder sb, Properties properties) {
        try (var stream = Files.lines(file)) {
            var propertyLines =
                    stream.takeWhile(line -> line.isBlank()).filter(it -> !it.startsWith("#"))
                            .map(String::trim)
                            .collect(Collectors.joining("\n"));
            sb.append(stream.collect(Collectors.joining("\n")));
            properties.load(new StringReader(propertyLines));
            //String[] entry = trimmed.split(" *[:=] *", 2);
            //if (entry.length > 1) {
            //    properties.put(entry[0], entry[1]);
            //}
        } catch (IOException e) {
            LOGGER.error("", e);
            return sb;
        }
        return sb;
    }

    /// Lists all examples in the given directory. This method is also accessed by the eclipse based
    /// projects.
    ///
    /// @param examplesDir The examples directory to list examples in.
    /// @return The found examples.
    public static List<Example> listExamples(File examplesDir) {
        Path base = examplesDir.toPath();
        Path index = base.resolve("index").resolve("samplesIndex.txt");
        try (var stream = Files.lines(index)) {
            return stream.map(String::trim)
                    .filter(it -> !it.startsWith("#") && !it.isEmpty())
                    .map(line -> {
                        try {
                            return loadExample(base.resolve(line));
                        } catch (IOException e) {
                            LOGGER.warn("Cannot parse example {}; ignoring it.", line, e);
                            return null;
                        }
                    })
                    .filter(Objects::nonNull)
                    .toList();
        } catch (IOException e) {
            LOGGER.warn("Error while reading samples", e);
        }
        return Collections.emptyList();
    }
}
