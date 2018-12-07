package consistencyChecking;

import java.nio.file.Path;
import org.key_project.util.collection.ImmutableList;

public interface Checker {
    public boolean check(ImmutableList<Path> paths);
}
