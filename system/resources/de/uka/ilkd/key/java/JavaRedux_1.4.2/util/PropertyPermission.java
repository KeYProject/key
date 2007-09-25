


package java.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamField;
import java.security.BasicPermission;
import java.security.Permission;
import java.security.PermissionCollection;
public final class PropertyPermission extends BasicPermission {
    transient int actions;
    public PropertyPermission(String name, String actions) {}
    private void setActions(String str) {}
    private void readObject(ObjectInputStream s)
     throws IOException, ClassNotFoundException {}
    private void writeObject(ObjectOutputStream s) throws IOException {}
    public boolean implies(Permission p) {}
    public boolean equals(Object obj) {}
    public int hashCode() {}
    public String getActions() {}
    public PermissionCollection newPermissionCollection() {}
}
