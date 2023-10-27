/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.io.*;
import java.nio.channels.Channels;
import java.nio.channels.ReadableByteChannel;
import java.nio.charset.CodingErrorAction;
import java.nio.charset.StandardCharsets;
import java.util.zip.GZIPInputStream;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;

/**
 * This file rule source derivative wraps its input stream into a {@link GZIPInputStream} thus
 * allowing decompressing gnu-zipped proof files.
 *
 * @author tbormer on 12.02.16.
 */
public class GZipFileRuleSource extends FileRuleSource {

    /**
     * Instantiates a new file rule source.
     *
     * This is only instantiated from {@link RuleSourceFactory#initRuleFile(File, boolean)}.
     *
     * @param ruleFile the file to read from.
     */
    GZipFileRuleSource(File ruleFile) {
        super(ruleFile);
    }

    @Override
    public InputStream getNewStream() {
        try {
            return new GZIPInputStream(new FileInputStream(ruleFile));
        } catch (IOException e) {
            throw new RuntimeException("Error while reading rules.", e);
        }
    }

    @Override
    public CharStream getCharStream() throws IOException {
        try (ReadableByteChannel channel = Channels.newChannel(getNewStream())) {
            return CharStreams.fromChannel(channel, StandardCharsets.UTF_8, 4096,
                CodingErrorAction.REPLACE, file().toString(), -1);
        }
    }
}
