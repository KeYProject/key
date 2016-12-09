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
 * 
 * An alternative is to pass-through pointers non-statically to the places where
 * they are needed. This again results results in inconvenient clutter in the
 * code.
 * 
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
    public static final File KEY_HOME;

    public static final File EXAMPLE_DIR;

    public static final File KEY_CORE_TEST;

    protected static final File RUNALLPROOFS_DIR;

    

    /**
     * Initialise static variables which are identical for each RAP run.
     */
    static {
        KEY_HOME = IOUtil.getProjectRoot(RunAllProofsTest.class)
                .getParentFile();
        EXAMPLE_DIR = new File(KEY_HOME, "key.ui" + File.separator + "examples");
        KEY_CORE_TEST = new File(KEY_HOME, "key.core.test");
        RUNALLPROOFS_DIR = new File(KEY_CORE_TEST, "testresults"
                + File.separator + "runallproofs");
    }

    public RunAllProofsDirectories(Date runStart) {
        RUNALLPROOFS_DIR.mkdirs();
    }

}
