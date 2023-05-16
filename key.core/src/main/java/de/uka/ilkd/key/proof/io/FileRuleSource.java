package de.uka.ilkd.key.proof.io;

import java.io.*;
import java.net.MalformedURLException;
import java.net.URL;
import java.nio.file.Path;
import java.util.Objects;
import javax.annotation.Nonnull;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;

public class FileRuleSource extends RuleSource {

    /**
     * The non-<code>null</code> reference to the file from which rules are read.
     */
    protected @Nonnull final Path ruleFile;

    private final long numberOfChars;

    FileRuleSource(Path ruleFile) {
        this.ruleFile = Objects.requireNonNull(ruleFile);
        numberOfChars = ruleFile.toFile().length();
    }

    @Override
    public int getNumberOfBytes() {
        return (int) numberOfChars;
    }

    @Override
    public @Nonnull Path file() {
        return ruleFile;
    }

    @Override
    public URL url() throws IOException {
        return file().toUri().toURL();
    }

    @Override
    public String getExternalForm() {
        try {
            return ruleFile.toUri().toURL().toExternalForm();
        } catch (final MalformedURLException exception) {
            // should not be thrown
            throw new RuntimeException(exception);
        }
    }

    @Override
    public InputStream getNewStream() {
        try {
            return new BufferedInputStream(new FileInputStream(ruleFile.toFile()));
        } catch (final FileNotFoundException exception) {
            throw new RuntimeException("Error while opening a file stream to " + ruleFile,
                exception);
        }
    }

    @Override
    public String toString() {
        return ruleFile.toString();
    }

    @Override
    public CharStream getCharStream() throws IOException {
        return CharStreams.fromPath(ruleFile.toAbsolutePath());
    }
}
