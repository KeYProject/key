/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.IOException;
import java.io.Writer;

import org.jspecify.annotations.NonNull;


/**
 * A {@link TeeReader} writes everything it writes to a separated writer.
 *
 * @author Alexander Weigl
 * @version 1 (10/3/21)
 */
public class TeeWriter extends Writer {

    private final @NonNull Writer source;
    private final @NonNull Writer sink;

    public TeeWriter(@NonNull Writer source, @NonNull Writer sink) {
        this.source = source;
        this.sink = sink;
    }

    @Override
    public void write(char[] cbuf, int off, int len) throws IOException {
        source.write(cbuf, off, len);
        sink.write(cbuf, off, len);
    }

    @Override
    public void flush() throws IOException {
        source.flush();
        sink.flush();
    }

    @Override
    public void close() throws IOException {
        source.close();
    }
}
