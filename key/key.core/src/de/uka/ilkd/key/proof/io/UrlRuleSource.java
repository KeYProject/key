package de.uka.ilkd.key.proof.io;

import java.io.*;
import java.net.URL;

public class UrlRuleSource
        extends RuleSource {

    private final URL url;
    private final long numberOfBytes;

    UrlRuleSource(final URL url) {
        this.url = url;
        if ("file".equals(url.getProtocol())) {
            numberOfBytes = new File(url.getFile()).length();
        } else {
            numberOfBytes = countBytesByReadingStream();
        }
    }

    private long countBytesByReadingStream() {
        try {
            final InputStream input = url.openStream();
            long localNumberOfBytes = 0;
            for (int readValue = input.read(); readValue != -1; localNumberOfBytes++, readValue = input.read());
            input.close();
            return localNumberOfBytes;
        } catch (final IOException exception) {
            throw new RuntimeException(exception);
        }
    }

    @Override
    public int getNumberOfBytes() {
        return (int) numberOfBytes;
    }

    @Override
    public File file() {
        return new File(url.getFile());
    }

    @Override
    public String getExternalForm() {
        return url.toExternalForm();
    }

    @Override
    public InputStream getNewStream() {
        try {
            return url.openStream();
        } catch (final IOException exception) {
            throw new RuntimeException("Error while reading rules.", exception);
        }
    }

    @Override
    public String toString() {
        return url.toString();
    }
}
