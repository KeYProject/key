package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URL;

public class FileRuleSource extends RuleSource {

    /**
     * The non-<code>null</code> reference to the file from which rules are
     * read.
     */
    protected final File ruleFile;

    private long numberOfChars;

    FileRuleSource(final File ruleFile) {
        this.ruleFile = ruleFile;
        if (ruleFile != null) {
            numberOfChars = ruleFile.length();
        }
    }

    @Override
    public int getNumberOfBytes() {
        return (int) numberOfChars;
    }

    @Override
    public File file() {
        if(ruleFile == null) {
            throw new NullPointerException();
        }
        return ruleFile;
    }

    @Override
    public URL url() throws IOException {
        return file().toURI().toURL();
    }

    @Override
    public String getExternalForm() {
        try {
            return ruleFile.toURI().toURL().toExternalForm();
        } catch (final MalformedURLException exception) {
            // should not be thrown
            throw new RuntimeException(exception);
        }
    }   

    @Override
    public InputStream getNewStream() {
        try {
            return new FileInputStream(ruleFile);
        } catch (final FileNotFoundException exception) {
            throw new RuntimeException("Error while reading rules.", exception);
        }
    }

    @Override
    public String toString() {
        return ruleFile.toString();
    }
}
