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

// TODO DOC

class JavaReduxFileCollection implements FileCollection {

    /**
     * The location where the libraries to be parsed can be found. It will be
     * used as a resource path relative to the path of the package.
     */
    private static String JAVA_SRC_DIR = "JavaRedux";
    
    private List<String> resources = new ArrayList<String>();

    public JavaReduxFileCollection() throws IOException {
        
        String resourceString = JAVA_SRC_DIR
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

    public Walker createWalker(String extension) throws IOException {
        if (!".java".equals(extension)) {
            throw new IllegalStateException(
                    "This collection can only list .java files");
        }
        
        return new Walker(resources.iterator());

    }
    
    private static class Walker implements FileCollection.Walker {

        private Iterator<String> iterator;
        private String current = null;
        private URL currentURL = null;

        public Walker(Iterator<String> iterator) {
            this.iterator = iterator;
        }

        public DataLocation getCurrentDataLocation() throws NoSuchElementException {
            if(currentURL == null)
                throw new NoSuchElementException();
            
            return new URLDataLocation(currentURL);
        }

        public String getCurrentName() throws NoSuchElementException {
            return current;
        }
        
        public String getType() {
            return "internal";
        }

        public InputStream openCurrent() throws IOException, NoSuchElementException {
            if(current == null)
                throw new NoSuchElementException();
            
            if(currentURL == null) {
                throw new FileNotFoundException("cannot find " + JAVA_SRC_DIR + "/" + current);
            }
            
            return currentURL.openStream();
        }

        public boolean step() {
            if(!iterator.hasNext()) {
                current = null;
                currentURL = null;
                return false;
            }
            
            current = iterator.next();
            
            // may be null!
            currentURL = KeYResourceManager.getManager().getResourceFile(
                    Recoder2KeY.class, JAVA_SRC_DIR + "/" + current);

            return true;
        }
        
    }

}
