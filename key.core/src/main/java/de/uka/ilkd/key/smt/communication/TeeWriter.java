package de.uka.ilkd.key.smt.communication;

import javax.annotation.Nonnull;
import java.io.IOException;
import java.io.Writer;


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
