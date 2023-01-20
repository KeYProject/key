/*
 * @(#)Extern.java	1.10 00/02/02
 *
 * Copyright 1997-2000 Sun Microsystems, Inc. All Rights Reserved.
 * 
 * This software is the proprietary information of Sun Microsystems, Inc.  
 * Use is subject to license terms.
 * 
 */



import com.sun.tools.doclets.*;
import com.sun.javadoc.*;
import java.util.Map;
import java.util.HashMap;
import java.io.*;
import java.net.*;

/**
 * Process and manage "-link" and "-linkoffline" to external packages. The 
 * options "-link" and "-linkoffline" both depend on the fact that Javadoc now 
 * generates "package-list"(lists all the packages which are getting 
 * documented) file in the current or the destination directory, while
 * generating the documentation.
 *
 * @author Atul M Dambalkar
 * @author Robert Field
 */
public class Extern {

    /**
     * Map package names on to this object.
     */
    static private Map packageMap;

    /**
     * Package name, found in the "package-list" file in the {@link path}.
     */
    final String packageName;
 
    /**
     * The URL or the directory path at which the package documentation will be
     * avaliable.
     */
    final String path;

    /**
     * If given path is directory path then true else if it is a URL then false.
     */
    final boolean relative;

    /**
     * Constructor to build a Extern object and map it with the package name.
     * If the same package name is found in the map, then the first mapped
     * Extern object or offline location will be retained.
     *
     * @param packagename Package name found in the "package-list" file.
     * @param path        URL or Directory path from where the "package-list"
     * file is picked.
     * @param relative    True if path is URL, false if directory path.
     */
    Extern(String packageName, String path, boolean relative) {
        this.packageName = packageName;
        this.path = path;
        this.relative = relative;
        if (packageMap == null) {
            packageMap = new HashMap();
        }
        if (!packageMap.containsKey(packageName)) { // save the previous 
	  packageMap.put(packageName, this);        // mapped location
        }
    }

    /**
     * Get the "Extern" object associated with this package name.
     *
     * @param pkgname Package name.
     */
    public static Extern findPackage(String pkgName) {
        if (packageMap == null) {
            return null;
        }
        return (Extern)packageMap.get(pkgName);
    }

    /**
     * Build the extern package list from given URL or the directory path. 
     * Flag error if the "-link" or "-linkoffline" option is already used.
     * 
     * @param url        URL or Directory path.
     * @param pkglisturl This can be another URL for "pacakge-list" or ordinary
     * file.
     */
    public static boolean url(String url, String pkglisturl,
                              DocErrorReporter reporter) {
        String errMsg = composeExternPackageList(url, pkglisturl);
        if (errMsg != null) {
            reporter.printError(errMsg);
            return false;
        } else {
            return true;
        }
    } 
        
    /**
     * Adjusts the end file separator if it is missing from the URL or the 
     * directory path and depending upon the URL or file path, it fetches or 
     * reads the "package-list" file.
     *
     * @param url        URL or the directory path.
     * @param pkglisturl URL for the "package-list" file or the "package-list" 
     * file itself.
     */
    static String composeExternPackageList(String url, String pkglisturl) {
        url = adjustEndFileSeparator(url);
        pkglisturl = adjustEndFileSeparator(pkglisturl);
        if (pkglisturl.startsWith("http://") ||   
            pkglisturl.startsWith("file:")) {
            return fetchURLComposeExternPackageList(url, pkglisturl);
        } else {
            return readFileComposeExternPackageList(url, pkglisturl);
        }                   
    }

    /**
     * If the URL or Directory path is missing end file separator, add that.
     */
    static String adjustEndFileSeparator(String url) {
        String filesep = isRelativePath(url)? File.separator: "/";
        if (!url.endsWith(filesep)) {
            url += filesep; 
        }
        return url;
    }

    /**
     * Return true if it's a relative file path and does not start with 
     * "http://" or "file:" string.
     */
    static boolean isRelativePath(String url) {
        return !(url.startsWith("http://") || url.startsWith("file:"));
    }

    /**
     * Retrieve the text from the resource bundle.
     * 
     * @param prop Message key.
     * @param link Message argument.
     */
    private static String getText(String prop, String link) {
        return Standard.configuration().standardmessage.getText(prop, link);
    }

    /**
     * Retrieve the text from the resource bundle.
     * 
     * @param msg Message key.
     */
    private static String getText(String msg) {
        return Standard.configuration().standardmessage.getText(msg);
    }

    /**
     * Fetch the URL and read the "package-list" file.
     *
     * @param urlpath        Path to the packages.
     * @param pkglisturlpath URL or the path to the "package-list" file.
     */
    static String fetchURLComposeExternPackageList(String urlpath, 
                                                   String pkglisturlpath) {
        String link = pkglisturlpath + "package-list"; 
        try {
            boolean relative = isRelativePath(urlpath);
            readPackageList((new URL(link)).openStream(), urlpath, relative);
        } catch (MalformedURLException exc) {
            return getText("doclet.MalformedURL", link);
        } catch (IOException exc) {
            return getText("doclet.URL_error", link);
        } 
        return null;
    }

    /**
     * Read the "package-list" file which is available locally.
     *
     * @param urlpath URL or Directory path to hte packages.
     * @param relpath Path to the local "package-list" file.
     */
    static String readFileComposeExternPackageList(String urlpath, 
                                                   String relpath) {
        String link = relpath + "package-list";
        try {
            File file = new File(link);    
            if (file.exists() && file.canRead()) {
                boolean relative = isRelativePath(urlpath);
                readPackageList(new FileInputStream(file), urlpath, relative);
            } else {
                return getText("doclet.File_error", link);
            }
        } catch (FileNotFoundException exc) {
            return getText("doclet.File_error", link);
        } catch (IOException exc) {
            return getText("doclet.File_error", link);
        }
        return null;
    }
     
    /**               
     * Read the file "package-list" and for each package name found, create
     * Extern object and associate it with the package name in the map.
     *
     * @param input    InputStream from the "package-list" file.
     * @param path     URL or the directory path to the packages.
     * @param relative Is path relative?
     */
    static void readPackageList(InputStream input, String path, 
                                boolean relative)  
                         throws IOException {
        InputStreamReader in = new InputStreamReader(input);
        StringBuffer strbuf = new StringBuffer();
        try {
            int c;
            while ((c = in.read()) >= 0) {
                char ch = (char)c;
                if (ch == '\n' || ch == '\r') {
                    if (strbuf.length() > 0) {
                        String packname = strbuf.toString();
                        String packpath = path + 
                                      packname.replace('.', '/') + '/';
                        new Extern(packname, packpath, relative); 
                        strbuf.setLength(0);
                    }
                } else {
                    strbuf.append(ch);
                }
            }
        } finally {
            input.close();
        } 
    }     

    /**
     * String representation of "this" with packagename and the path.
     */
    public String toString() {
        return packageName + (relative? " -> " : " => ") + path;
    }
} 
        

