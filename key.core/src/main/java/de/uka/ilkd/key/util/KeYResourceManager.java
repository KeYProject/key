/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.*;
import java.net.URL;
import java.nio.channels.Channels;
import java.nio.channels.ReadableByteChannel;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * KeYResourceManager controls the access to the properties and resources used in the KeY system.
 * Use the static method getManager to get the unique instance.
 */
public class KeYResourceManager {
    private static final Logger LOGGER = LoggerFactory.getLogger(KeYResourceManager.class);

    private static final String DEFAULT_VERSION = "x.z.y";
    private static final Set<String> INVISIBLE_BRANCHES =
        Set.of("master", "main");

    /**
     * the unique instance
     */
    private static final KeYResourceManager instance = new KeYResourceManager();


    private String version = null;
    private String sha1 = null;
    private String branch = null;

    private KeYResourceManager() {
    }

    /**
     * Return an instance of the ResourceManager
     */
    public static KeYResourceManager getManager() {
        return instance;
    }


    /**
     * reads a version string or returns "x.z.y" in case of failures
     */
    private String readVersionString(URL url) {
        StringBuilder result = new StringBuilder();
        if (url != null) {
            try (InputStream io = new BufferedInputStream(url.openStream())) {
                int c;
                while ((c = io.read()) != -1) {
                    result.append((char) c);
                }
            } catch (IOException ioe) {
                // who cares it is just a version number
                result = new StringBuilder(DEFAULT_VERSION);
            }
            // then leave it open
        } else {
            result = new StringBuilder(DEFAULT_VERSION);
        }
        return result.toString().trim();
    }

    /**
     * returns the SHA 1 git code from which this version has been derived
     *
     * @return returns the SHA1 hash uniquely identifying the version
     */
    public String getSHA1() {
        if (sha1 != null) {
            return sha1;
        }
        sha1 = readVersionString(getResourceFile(this, "sha1"));

        return sha1;
    }

    /**
     * returns the git branch from which this version has been derived
     *
     * @return returns the git branch partially identifying the version
     */
    public String getBranch() {
        if (branch != null) {
            return branch;
        }
        branch = readVersionString(getResourceFile(this, "branch"));

        return branch;
    }

    public boolean visibleBranch() {
        final String b = getBranch();
        final String v = getVersion();
        return !b.equals("") && !INVISIBLE_BRANCHES.contains(b) && !b.startsWith("KeY" + v)
                && !b.startsWith("KeY" + "-" + v);
    }

    /**
     * returns a readable customizable version number
     *
     * @return a readable version number
     */
    public String getVersion() {
        if (version != null) {
            return version;
        }
        version = readVersionString(getResourceFile(this, "version"));

        return version;
    }

    /**
     * Copies the specified resource to targetLocation if such a file does not exist yet. The
     * created file is removed automatically after finishing JAVA.
     *
     * @param o an Object the directory from where <code>resourcename</code> is copied is determined
     *        by looking on the package where <code>o.getClass()</code> is declared
     * @param resourcename String the name of the file to search (only relative pathname to the path
     *        of the calling class)
     * @param targetLocation target for copying
     * @return true if resource was copied
     */
    public boolean copyIfNotExists(Object o, String resourcename, String targetLocation) {
        return copyIfNotExists(o.getClass(), resourcename, targetLocation);
    }

    public boolean copyIfNotExists(Class<?> cl, String resourcename, String targetLocation) {
        return copy(cl, resourcename, targetLocation, false);
    }

    public boolean copy(Class<?> cl, String resourcename, String targetLocation,
            boolean overwrite) {
        URL resourceURL = cl.getResource(resourcename);

        LOGGER.debug("Load Resource:" + resourcename + " of class " + cl);

        if (resourceURL == null && cl.getSuperclass() != null) {
            return copy(cl.getSuperclass(), resourcename, targetLocation, overwrite);
        } else if (resourceURL == null) {
            // error message Resource not found
            LOGGER.warn("No resource " + resourcename + " found");
            return false;
        }

        // copying the resource to the target if targetfile
        // does not exist yet
        boolean result = false;
        try {
            File targetFile = new File(targetLocation);
            if (overwrite || !targetFile.exists()) {
                result = true;
                if (targetFile.getParentFile() != null && !targetFile.getParentFile().exists()) {
                    if (!targetFile.getParentFile().mkdirs()) {
                        throw new IOException("Could not create " + targetFile.getParentFile());
                    }
                }
                targetFile.createNewFile();
                targetFile.deleteOnExit();


                long actualTransferredByte;
                try (ReadableByteChannel sourceStream =
                    Channels.newChannel(resourceURL.openStream());
                        FileOutputStream out = new FileOutputStream(targetFile)) {
                    actualTransferredByte =
                        out.getChannel().transferFrom(sourceStream, 0, Long.MAX_VALUE);
                }
                if (actualTransferredByte < 0 || actualTransferredByte == Long.MAX_VALUE) {
                    throw new RuntimeException("File " + resourcename + " too big.");
                }
            }
        } catch (Exception e) {
            LOGGER.debug("KeYError: " + e);
            return false;
        }

        return result;
    }


    /**
     * loads a resource and returns its URL
     *
     * @param cl the Class used to determine the resource
     * @param resourcename the String that contains the name of the resource
     * @return the URL of the resource
     */
    public URL getResourceFile(Class<?> cl, String resourcename) {
        URL resourceURL = cl.getResource(resourcename);
        if (resourceURL == null && cl.getSuperclass() != null) {
            return getResourceFile(cl.getSuperclass(), resourcename);
        } else if (resourceURL == null && cl.getSuperclass() == null) {
            return null;
        }
        return resourceURL;
    }

    /**
     * loads a resource and returns its URL
     *
     * @param o the Object used to determine the resource
     * @param resourcename the String that contains the name of the resource
     * @return the URL of the resource
     */
    public URL getResourceFile(Object o, String resourcename) {
        return getResourceFile(o.getClass(), resourcename);
    }

    /**
     * All KeY {@link de.uka.ilkd.key.control.UserInterfaceControl}s should use a common title
     * string when they require one, for instance for a GUI window title bar.
     *
     * @return the title string to be used by the KeY <code>UserInterfaces</code>
     */
    public String getUserInterfaceTitle() {
        return String.format("KeY %s%s", this.getVersion(),
            visibleBranch() ? " [" + getBranch() + "]" : "");
    }
}
