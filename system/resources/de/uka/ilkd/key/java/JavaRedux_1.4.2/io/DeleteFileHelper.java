

package java.io;

import java.security.AccessController;
import java.security.PrivilegedAction;
import java.util.ArrayList;
import java.util.Iterator;
final class DeleteFileHelper extends Thread {

    static synchronized void add(File file) {}

    private static synchronized void deleteFiles() {}

    private DeleteFileHelper() {}

    public void run() {}
}
