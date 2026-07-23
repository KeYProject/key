/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.channels.Channels;
import java.nio.channels.ReadableByteChannel;
import java.nio.charset.CodingErrorAction;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.HashMap;

import org.key_project.util.java.StringUtil;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;

public class UrlRuleSource extends RuleSource {

    private final URL url;
    private final long numberOfBytes;

    UrlRuleSource(final URL url) {
        this.url = url;
        if ("file".equals(url.getProtocol())) {
            numberOfBytes = fileSizeOrCountStream();
        } else {
            numberOfBytes = countBytesByReadingStream();
        }
    }

    private long fileSizeOrCountStream() {
        try {
            // Resolve the file via the URI (like file()) rather than url.getFile(): the latter is
            // not percent-decoded and keeps the leading '/' of "file:/C:/..." on Windows, so for
            // paths containing spaces (%20) or on Windows it would point at a non-existent file and
            // report a length of 0.
            return Files.size(Paths.get(url.toURI()));
        } catch (URISyntaxException | IOException e) {
            return countBytesByReadingStream();
        }
    }

    private long countBytesByReadingStream() {
        try {
            final InputStream input = url.openStream();
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
    public Path file() {
        try {
            var uri = url.toURI();
            try {
                return Paths.get(uri);
            } catch (FileSystemNotFoundException e) {
                URI rootFs = URI.create(StringUtil.takeUntil(uri.toString(), "!"));
                String internal = StringUtil.takeAfter(uri.toString(), "!");
                // keep the file system open.
                FileSystem zipfs = FileSystems.newFileSystem(rootFs, new HashMap<>());
                return zipfs.getPath(internal);
            }
        } catch (URISyntaxException | IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public URL url() {
        return url;
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

    @Override
    public CharStream getCharStream() throws IOException {
        try (ReadableByteChannel channel = Channels.newChannel(getNewStream())) {
            return CharStreams.fromChannel(channel, StandardCharsets.UTF_8, 4096,
                CodingErrorAction.REPLACE, url.toString(), -1);
        }
    }
}
