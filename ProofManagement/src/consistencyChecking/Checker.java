package consistencyChecking;

import java.nio.file.Path;
import java.util.List;

public interface Checker {
    public boolean check(List<Path> paths);
}
