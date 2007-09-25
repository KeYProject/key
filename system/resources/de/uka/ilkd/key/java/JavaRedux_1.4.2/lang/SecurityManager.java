


package java.lang;

import java.awt.AWTPermission;
import java.io.File;
import java.io.FileDescriptor;
import java.io.FilePermission;
import java.lang.reflect.Member;
import java.net.InetAddress;
import java.net.SocketPermission;
import java.security.AccessControlContext;
import java.security.AccessController;
import java.security.AllPermission;
import java.security.Permission;
import java.security.Security;
import java.security.SecurityPermission;
import java.util.PropertyPermission;
public class SecurityManager {
    protected boolean inCheck;
    public SecurityManager() {}
    public boolean getInCheck() {}
    protected Class[] getClassContext() {}
    protected ClassLoader currentClassLoader() {}
    protected Class currentLoadedClass() {}
    protected int classDepth(String className) {}
    protected int classLoaderDepth() {}
    protected boolean inClass(String className) {}
    protected boolean inClassLoader() {}
    public Object getSecurityContext() {}
    public void checkPermission(Permission perm) {}
    public void checkPermission(Permission perm, Object context) {}
    public void checkCreateClassLoader() {}
    public void checkAccess(Thread thread) {}
    public void checkAccess(ThreadGroup g) {}
    public void checkExit(int status) {}
    public void checkExec(String program) {}
    public void checkLink(String filename) {}
    public void checkRead(FileDescriptor desc) {}
    public void checkRead(String filename) {}
    public void checkRead(String filename, Object context) {}
    public void checkWrite(FileDescriptor desc) {}
    public void checkWrite(String filename) {}
    public void checkDelete(String filename) {}
    public void checkConnect(String host, int port) {}
    public void checkConnect(String host, int port, Object context) {}
    public void checkListen(int port) {}
    public void checkAccept(String host, int port) {}
    public void checkMulticast(InetAddress addr) {}
    public void checkMulticast(InetAddress addr, byte ttl) {}
    public void checkPropertiesAccess() {}
    public void checkPropertyAccess(String key) {}
    public boolean checkTopLevelWindow(Object window) {}
    public void checkPrintJobAccess() {}
    public void checkSystemClipboardAccess() {}
    public void checkAwtEventQueueAccess() {}
    public void checkPackageAccess(String packageName) {}
    public void checkPackageDefinition(String packageName) {}
    public void checkSetFactory() {}
    public void checkMemberAccess(Class c, int memberType) {}
    public void checkSecurityAccess(String action) {}
    public ThreadGroup getThreadGroup() {}
    void checkPackageList(String packageName, String restriction,
                        String permission) {}
}
class SecurityContext {
        Class[] classes;
        SecurityContext(Class[] classes) {}
}
