/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.IOException;
import java.io.Writer;
import javax.annotation.Nonnull;


/**
 * A {@link TeeReader} writes everything it writes to a separated writer.
 *
 * @author Alexander Weigl
 * @version 1 (10/3/21)
 */
public class TeeWriter extends Writer {
    @Nonnull
    private final Writer source;

    @Nonnull
    private final Writer sink;

    public TeeWriter(@Nonnull Writer source, @Nonnull Writer sink) {
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
