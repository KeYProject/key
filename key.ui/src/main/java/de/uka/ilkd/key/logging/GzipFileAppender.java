package de.uka.ilkd.key.logging;

import ch.qos.logback.core.FileAppender;
import ch.qos.logback.core.recovery.ResilientFileOutputStream;
import ch.qos.logback.core.util.FileSize;
import ch.qos.logback.core.util.FileUtil;

import java.io.File;
import java.io.IOException;
import java.util.zip.GZIPOutputStream;

/**
 * @author Alexander Weigl
 * @version 1 (20.03.23)
 */
public class GzipFileAppender<E> extends FileAppender<E> {
    private final FileSize bufferSize = new FileSize(DEFAULT_BUFFER_SIZE);

    @Override
    public void openFile(String file_name) throws IOException {
        lock.lock();
        try {
            File file = new File(file_name);
            boolean result = FileUtil.createMissingParentDirectories(file);
            if (!result) {
                addError(
                    "Failed to create parent directories for [" + file.getAbsolutePath() + "]");
            }

            ResilientFileOutputStream resilientFos =
                new ResilientFileOutputStream(file, append, bufferSize.getSize());
            resilientFos.setContext(context);
            var gzip = new GZIPOutputStream(resilientFos);
            setOutputStream(gzip);
        } finally {
            lock.unlock();
        }
    }
}
