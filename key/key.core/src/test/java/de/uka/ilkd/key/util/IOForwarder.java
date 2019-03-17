package de.uka.ilkd.key.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

/**
 * A simple i/o forwarding thread which maps {@link InputStream}s to
 * {@link OutputStream}s.
 *
 * Used to redirect i/o from {@link Process}es to system streams.
 *
 * The class is active and the threads terminate as soon as the input stream is
 * at EOF.
 *
 * NB: {@link ProcessBuilder#inheritIO()} would not work.
 *
 * @author Mattias Ulbrich
 */
public class IOForwarder extends Thread {


    private final InputStream from;
    private final OutputStream to;

    public IOForwarder(String type, InputStream from, OutputStream to) {
        super("IOForwarder - " + type);
        this.from = from;
        this.to = to;
    }

    /**
     * Forward the stdout and stderr streams of process to System.out and
     * System.err.
     *
     * This method launches two new threads.
     *
     * @param process
     *            process whose output is to be forwarded.
     */
    public static void forward(Process process) {
//        IOForwarder f1 = new IOForwarder("stdin", System.in, process.getOutputStream());
//        f1.start();
        IOForwarder f2 = new IOForwarder("stdout", process.getInputStream(), System.out);
        f2.start();
        IOForwarder f3 = new IOForwarder("stderr", process.getErrorStream(), System.err);
        f3.start();
    }

    @Override
    public void run() {
        try {
            byte buffer[] = new byte[4096];
            int read = 0;
            while((read=from.read(buffer)) > 0) {
                to.write(buffer, 0, read);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

}
