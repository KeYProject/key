package de.uka.ilkd.key.smt.communication;

import org.jspecify.annotations.NonNull;
import java.io.IOException;
import java.io.Reader;
import java.io.Writer;

/**
 * A {@link TeeReader} writes everything it reads to a separated writer.
 *
 * @author Alexander Weigl
 * @version 1 (10/3/21)
 */
public class TeeReader extends Reader {
    @NonNull
    private final Reader source;

    @NonNull
    private final Writer sink;

    public TeeReader(@NonNull Reader source, @NonNull Writer sink) {
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
