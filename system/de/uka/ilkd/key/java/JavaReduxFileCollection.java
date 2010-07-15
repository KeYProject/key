package de.uka.ilkd.key.java;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import recoder.io.DataLocation;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.recoderext.URLDataLocation;
import de.uka.ilkd.key.util.FileCollection;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * This is a special {@link FileCollection} which allows to retrieve the
 * internally stored java boot sources and to iterate over them.
 * 
 * <p>
 * The resources are stored in the binaries. We use the
 * {@link KeYResourceManager} to find the resources.
 * 
 * <p>
 * There is a text file whose name is given by
 * {@link de.uka.ilkd.key.proof.init.Profile#getInternalClasslistFilename()}
 * which enumerates all java files that have to be read.
 * 
 * @author mulbrich
 */
class JavaReduxFileCollection implements FileCollection {

    /**
     * The location where the libraries to be parsed can be found. It will be
     * used as a resource path relative to the path of the package.
     */
    private static String JAVA_SRC_DIR = "JavaRedux";

    /**
     * The resource location
     */
    private String resourceLocation;

    
    /**
     * This list stores all resources to be retrieved. It is fed by the
     * constructor.
     */
    private List<String> resources = new ArrayList<String>();

    /**
     * Instantiates a new file collection.
     * 
     * The list of resources is retreived and interpreted. The resources
     * themselves are not yet read.
     * 
     * @throws IOException
     *             if access to the resources fails
     */
    public JavaReduxFileCollection() throws IOException {

	resourceLocation = JAVA_SRC_DIR
	        + "/"
	        + ProofSettings.DEFAULT_SETTINGS.getProfile()
	                .getInternalClassDirectory();

	String resourceString = resourceLocation
	        + "/"
	        + ProofSettings.DEFAULT_SETTINGS.getProfile()
	                .getInternalClasslistFilename();

	URL jlURL = KeYResourceManager.getManager().getResourceFile(
	        Recoder2KeY.class, resourceString);
	
        if (jlURL == null) {
            throw new FileNotFoundException("Resource " + resourceString
                    + " cannot be opened.");
        }

        BufferedReader r = new BufferedReader(new InputStreamReader(jlURL
                .openStream()));

        for (String jl = r.readLine(); (jl != null); jl = r.readLine()) {
            // ignore comments and empty lines
            if ((jl.length() == 0) || (jl.charAt(0) == '#')) {
                continue;
            }

            resources.add(jl);
        }

    }

    /**
     * {@inheritDoc}
     * 
     * This class only supports walker for a single file type: .java
     */
    public Walker createWalker(String extension) throws IOException {
        if (!".java".equals(extension)) {
            throw new IllegalStateException(
                    "This collection can only list .java files");
        }

        return new Walker(resources.iterator());

    }

    /**
     * {@inheritDoc}
     * 
     * This class only supports walker for a single file type: .java
     */
    public Walker createWalker(String[] extensions) throws IOException {
        if (extensions == null || extensions.length < 1 || !".java".equals(extensions[0])) {
            throw new IllegalStateException(
                    "This collection can only list .java files");
        }

        return new Walker(resources.iterator());

    }

    /*
     * The Class Walker wraps a string iterator and creates URL, streams and
     * DataLocation elements on demand.
     */
    private class Walker implements FileCollection.Walker {

        /**
         * The iterator to wrap, it iterates the resources to open.
         */
        private Iterator<String> iterator;

        /**
         * The currently open resource. null before the first step and after the last step.
         */
        private String current = null;

        /**
         * The URL of the current resource.
         */
        private URL currentURL = null;

        
        private Walker(Iterator<String> iterator) {
            this.iterator = iterator;
        }

        public DataLocation getCurrentDataLocation()
                throws NoSuchElementException {
            if (currentURL == null)
                throw new NoSuchElementException();

            return new URLDataLocation(currentURL);
        }

        public String getCurrentName() throws NoSuchElementException {
            return current;
        }

        public String getType() {
            return "internal";
        }

        public InputStream openCurrent() throws IOException,
                NoSuchElementException {
            if (current == null)
                throw new NoSuchElementException();

            if (currentURL == null) {
                throw new FileNotFoundException("cannot find "  
                	+ resourceLocation 
                        + "/" + current);
            }

            return currentURL.openStream();
        }

        public boolean step() {
            if (!iterator.hasNext()) {
                current = null;
                currentURL = null;
                return false;
            }

            current = iterator.next();

            // may be null!
            currentURL = KeYResourceManager.getManager().getResourceFile(
                    Recoder2KeY.class, resourceLocation + "/" + current);

            return true;
        }

    }

}
