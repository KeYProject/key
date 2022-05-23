package de.uka.ilkd.key.smt;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.concurrent.TimeUnit;

/**
 * Little helper class that helps to check for the version of a solver. Mainly it provides
 * a method that starts the solver using certain parameters in order to obtain the version of that
 * solver.
 */
public class VersionChecker {
    public static final VersionChecker INSTANCE = new VersionChecker();

    private static final long MAX_DELAY = 1000;

    public String getVersionFor(String command, String parameter) {
        ProcessBuilder pb = new ProcessBuilder(command, parameter);
        Process p = null;
        try {
            p = pb.start();
            p.waitFor(MAX_DELAY, TimeUnit.MILLISECONDS);
            try (BufferedReader r = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
                String line = r.readLine();
                // TODO weigl for Java 11 use "p.destroyForcibly();"                
                return line;
            }
        } catch (Exception e) {
            throw new RuntimeException(e);
        } finally{
            if( p != null && p.isAlive() ) {
                p.destroy();
            }
        }
    }
}
