package de.uka.ilkd.key.testgen;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.Objects;

/**
 * @author Alexander Weigl
 * @version 1 (02.02.24)
 */
public record OutputEnvironment(Path targetFolder) {
    public Path getSourceDir() {
        return targetFolder.resolve("src");
    }

    public Path getTestSourceDir() {
        return targetFolder.resolve("test");
    }

    public Path getAntFile() {
        return targetFolder.resolve("build.xml");
    }

    public Path getReadmeFile() {
        return targetFolder.resolve("README.md");
    }

    public void init() throws IOException {
        Files.createDirectories(getSourceDir());
        Files.createDirectories(getTestSourceDir());

        installAntFile();
    }

    private void installAntFile() throws IOException {
        try (var buildXml = getClass().getResourceAsStream("/de/uka/ilkd/key/tcg/build.xml")) {
            Files.copy(Objects.requireNonNull(buildXml), getAntFile(), StandardCopyOption.REPLACE_EXISTING);
        }
    }
}
