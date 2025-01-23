/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URL;
import java.nio.channels.Channels;
import java.nio.channels.ReadableByteChannel;
import java.nio.charset.CodingErrorAction;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;

public class UrlRuleSource extends RuleSource {

    private final URI uri;
    private final long numberOfBytes;

    UrlRuleSource(final URI url) {
        long tempSize;
        this.uri = url;
        try {
            var path = Paths.get(url);
            tempSize = Files.size(path);
        } catch (IOException e) {
            tempSize = countBytesByReadingStream();
        }
        numberOfBytes = tempSize;
    }

    private long countBytesByReadingStream() {
        try {
            final InputStream input = uri.toURL().openStream();
            long localNumberOfBytes = 0;
            for (int readValue = input.read(); readValue != -1; localNumberOfBytes++, readValue =
                    input.read()) {
            }
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
        return new File(url().getFile());
    }

    @Override
    public URL url() {
        try {
            return uri().toURL();
        } catch (MalformedURLException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public URI uri() {
        return uri;
    }

    @Override
    public String getExternalForm() {
        return url().toExternalForm();
    }

    @Override
    public InputStream getNewStream() {
        try {
            return url().openStream();
        } catch (final IOException exception) {
            throw new RuntimeException("Error while reading rules.", exception);
        }
    }

    @Override
    public String toString() {
        return uri.toString();
    }

    @Override
    public CharStream getCharStream() throws IOException {
        try (ReadableByteChannel channel = Channels.newChannel(getNewStream())) {
            return CharStreams.fromChannel(channel, StandardCharsets.UTF_8, 4096,
                    CodingErrorAction.REPLACE, uri.toString(), -1);
        }
    }
}
