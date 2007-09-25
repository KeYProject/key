

package java.lang;

import java.net.URL;
import java.util.NoSuchElementException;
import java.util.StringTokenizer;
public class Package {
    Package(String name,
          String specTitle, String specVendor, String specVersion,
          String implTitle, String implVendor, String implVersion, URL sealed) {}
    public String getName() {}
    public String getSpecificationTitle() {}
    public String getSpecificationVersion() {}
    public String getSpecificationVendor() {}
    public String getImplementationTitle() {}
    public String getImplementationVersion() {}
    public String getImplementationVendor() {}
    public boolean isSealed() {}
    public boolean isSealed(URL url) {}
    public boolean isCompatibleWith(String version) {}
    public static Package getPackage(String name) {}
    public static Package[] getPackages() {}
    public int hashCode() {}
    public String toString() {}
}
