/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

import de.uka.ilkd.key.util.ProgressMonitor;

import org.key_project.util.java.IOUtil;

public class CountingBufferedReader extends BufferedReader {

    private long chars;
    private int step = 0;
    private ProgressMonitor monitor = ProgressMonitor.Empty.getInstance();

    public CountingBufferedReader(InputStream in) {
        super(new InputStreamReader(in, IOUtil.DEFAULT_CHARSET));
        chars = 0;
        step = 1;
    }

    public CountingBufferedReader(InputStream in, ProgressMonitor monitor, int step) {
        this(in);
        this.step = (step == 0 ? 1 : step);
        this.monitor = monitor;
        chars = 0;
    }

    public CountingBufferedReader(InputStream in, ProgressMonitor monitor, int step,
            int alreadyRead) {
        this(in, monitor, step);
        chars = alreadyRead;
    }

    public CountingBufferedReader(InputStream in, int size, int step) {
        super(new InputStreamReader(in, IOUtil.DEFAULT_CHARSET), size);
        this.step = (step == 0 ? 1 : step);
        chars = 0;
    }

    private void incCharCounter(long inc) {
        chars += inc;
        if (monitor != null && chars % step == 0) {
            monitor.setProgress((int) chars);
        }
    }

    @Override
    public int read() throws IOException {
        final int readChar = super.read();
        if (readChar != -1) {
            incCharCounter(1);
        }
        return readChar;
    }

    @Override
    public int read(char[] cbuf, int off, int len) throws IOException {
        final int readChars = super.read(cbuf, off, len);
        if (readChars > 0) {
            incCharCounter(readChars);
        }
        return readChars;
    }

    @Override
    public String readLine() throws IOException {
        final String line = super.readLine();
        if (line != null) {
            incCharCounter(line.length());
        }
        return line;
    }

    @Override
    public long skip(long n) throws IOException {
        final long skippedChars = super.skip(n);
        if (skippedChars > 0) {
            incCharCounter(skippedChars);
        }
        return skippedChars;
    }
}
