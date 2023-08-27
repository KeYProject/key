/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A simple i/o forwarding thread which maps {@link InputStream}s to {@link OutputStream}s.
 * <p>
 * Used to redirect i/o from {@link Process}es to system streams.
 * <p>
 * The class is active and the threads terminate as soon as the input stream is at EOF.
 * <p>
 * NB: {@link ProcessBuilder#inheritIO()} would not work.
 *
 * @author Mattias Ulbrich
 */
public class IOForwarder extends Thread {
    private static final Logger LOGGER = LoggerFactory.getLogger(IOForwarder.class);

    private final InputStream from;
    private final OutputStream to;

    public IOForwarder(String type, InputStream from, OutputStream to) {
        super("IOForwarder - " + type);
        this.from = from;
        this.to = to;
    }

    /**
     * Forward the stdout and stderr streams of process to System.out and System.err.
     * <p>
     * This method launches two new threads.
     *
     * @param process process whose output is to be forwarded.
     */
    public static void forward(Process process) {
        IOForwarder f2 = new IOForwarder("stdout", process.getInputStream(), System.out);
        f2.start();
        IOForwarder f3 = new IOForwarder("stderr", process.getErrorStream(), System.err);
        f3.start();
    }

    @Override
    public void run() {
        try {
            byte[] buffer = new byte[4096];
            int read;
            while ((read = from.read(buffer)) > 0) {
                to.write(buffer, 0, read);
            }
        } catch (IOException e) {
            LOGGER.warn("Forward failed", e);
        }
    }

}
