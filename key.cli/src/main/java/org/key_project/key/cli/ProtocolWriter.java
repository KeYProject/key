/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;

/**
 * A {@link PrintWriter} that terminates every line with a single {@code '\n'} and flushes it,
 * independent of the platform.
 * <p>
 * The headless interface spec specifies byte-exact output (§2: the {@code KEY_RESULT} line is
 * "terminated by {@code \n}"; the §6/§7 markers and the §8 diagnostics are line-oriented), so the
 * platform line separator that {@link PrintWriter#println(String)} inserts on Windows must not
 * leak into the protocol.
 */
final class ProtocolWriter extends PrintWriter {

    /**
     * Creates a protocol writer over the given byte stream, encoding UTF-8.
     *
     * @param stream the stream to write to (stdout or stderr)
     */
    ProtocolWriter(OutputStream stream) {
        super(new OutputStreamWriter(stream, StandardCharsets.UTF_8));
    }

    @Override
    public void println(String line) {
        print(line);
        print('\n');
        flush();
    }

    @Override
    public void println() {
        print('\n');
        flush();
    }
}
