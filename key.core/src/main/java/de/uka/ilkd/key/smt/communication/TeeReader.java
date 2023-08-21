/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.IOException;
import java.io.Reader;
import java.io.Writer;
import javax.annotation.Nonnull;

/**
 * A {@link TeeReader} writes everything it reads to a separated writer.
 *
 * @author Alexander Weigl
 * @version 1 (10/3/21)
 */
public class TeeReader extends Reader {
    @Nonnull
    private final Reader source;

    @Nonnull
    private final Writer sink;

    public TeeReader(@Nonnull Reader source, @Nonnull Writer sink) {
        this.source = source;
        this.sink = sink;
    }

    @Override
    public int read(char[] cbuf, int off, int len) throws IOException {
        int r = source.read(cbuf, off, len);
        sink.write(cbuf, off, len);
        return r;
    }


    @Override
    public void close() throws IOException {
        source.close();
    }
}
