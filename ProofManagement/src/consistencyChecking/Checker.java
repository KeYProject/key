package consistencyChecking;

import java.nio.file.Path;
import org.key_project.util.collection.ImmutableList;

public interface Checker {
    /**
     * Checks the given proof files for consistency.
     * @param proofFiles the paths of the *.proof files to check
     * @return true if the files are consistent w.r.t this check and false if not
     */
    public boolean check(ImmutableList<Path> proofFiles);
}
