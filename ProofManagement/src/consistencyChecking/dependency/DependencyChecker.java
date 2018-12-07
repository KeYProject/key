package consistencyChecking;

import java.nio.file.Path;
import org.key_project.util.collection.ImmutableList;

public class DependencyChecker implements Checker {

    @Override
    public boolean check(ImmutableList<Path> paths) {
        return false;
    }
}
