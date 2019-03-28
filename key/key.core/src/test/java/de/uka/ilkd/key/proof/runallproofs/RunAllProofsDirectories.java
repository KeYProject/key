package de.uka.ilkd.key.proof.runallproofs;

import java.io.File;
import java.io.Serializable;
import java.util.Date;

import org.key_project.util.java.IOUtil;

/**
 * Initialising directories for runallproofs is a bit tricky since doing it
 * statically results easily in hard-to-detect bugs for forked mode of
 * runallproofs. Subprocesses have to re-initialise static variables correctly,
 * which could be overlooked or implemented incorrectly. Even if implemented
 * correctly, the resulting code can be quite complicated.
 * <p>
 * An alternative is to pass-through pointers non-statically to the places where
 * they are needed. This again results results in inconvenient clutter in the
 * code.
 * <p>
 * I eventually decided to put all filesystem-related stuff from runallproofs to
 * a separate location.
 *
 * @author kai
 */
@SuppressWarnings("serial")
public class RunAllProofsDirectories implements Serializable {

    /**
     * The path to the KeY repository. Configurable via system property
     * {@code key.home}.
     */
    public static final File EXAMPLE_DIR;
    protected static final File RUNALLPROOFS_DIR;


    /**
     * Initialise static variables which are identical for each RAP run.
     */
    static {
        EXAMPLE_DIR = findFolder("EXAMPLES_DIR", true,
                "examples", "../key.ui/examples", "key.ui/examples");
        RUNALLPROOFS_DIR = findFolder("RUNALLPROOFS_DIR", false,
                "testresults/runallproofs",
                "../testresults/runallproofs",
                "../key.core/testresults/runallproofs",
                "key.core/testresults/runallproofs");
    }

    private static File findFolder(String propertyName, boolean exists, String... candidates) {
        if (System.getProperty(propertyName) != null) {
            File f = new File(System.getProperty(propertyName));
            if (f.exists() || !exists) return f;
        }

        for (String c : candidates) {
            File f = new File(c);
            if (f.exists() || !exists) return f;
        }
        return null;
    }

    public RunAllProofsDirectories(Date runStart) {
        RUNALLPROOFS_DIR.mkdirs();
    }

}
