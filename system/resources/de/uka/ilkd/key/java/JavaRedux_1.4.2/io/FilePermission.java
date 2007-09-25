


package java.io;

import java.security.Permission;

public final class FilePermission extends Permission implements Serializable {
    static final long serialVersionUID = 7930732926638008763L;
    private void checkPerms() throws IllegalArgumentException {}
    public FilePermission(String pathExpression, String actionsString) {}
    public String getActions() {}
    public int hashCode() {}
    public boolean equals(Object o) {}
    public boolean implies(Permission p) {}
}
