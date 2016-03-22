package de.uka.ilkd.key.nui.prooftree;

import java.io.File;
import java.io.IOException;
import java.lang.annotation.Annotation;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.AbstractMap.SimpleImmutableEntry;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Observable;
import java.util.concurrent.ConcurrentHashMap;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import de.uka.ilkd.key.nui.DataModel;
import de.uka.ilkd.key.nui.prooftree.filter.FilterAnnotation;
import de.uka.ilkd.key.nui.prooftree.filter.FilterCombineAND;
import de.uka.ilkd.key.nui.prooftree.filter.FilterHideIntermediate;
import de.uka.ilkd.key.nui.prooftree.filter.FilterHideNonInteractive;
import de.uka.ilkd.key.nui.prooftree.filter.FilterHideNonSymbolicExecution;
import de.uka.ilkd.key.nui.prooftree.filter.FilterShowAll;
import de.uka.ilkd.key.nui.prooftree.filter.ProofTreeFilter;

/**
 * Handles the filtering of the proof tree.
 * 
 * @author Matthias Schultheis
 * @author Florian Breitfelder
 *
 */
public class FilteringHandler {

    /**
     * Prefix for binary class files.
     */
    private static final String BIN_NAME_PREFX = "de.uka.ilkd.key.nui.prooftree.filter.";

    /**
     * The data model.
     */
    private final DataModel dataModel;

    /**
     * A map storing filters with their respective activation flag.
     */
    final private Map<ProofTreeFilter, Boolean> filtersMap = Collections
            .synchronizedMap(new ConcurrentHashMap<>());

    /**
     * Constructor.
     * 
     * @param model
     *            The DataModel.
     * @throws FileNotFoundException
     */
    public FilteringHandler(final DataModel model) {
        this.dataModel = model;

        // Load filters and store all loaded filters into the filtersMap
        final List<ProofTreeFilter> filters = searchFilterClasses();
        filters.forEach((filter) -> filtersMap.put(filter, false));

        // Reinitialize filters if the data model changed
        model.addObserver((final Observable obs, final Object arg) -> {
            reinit();
        });
    }

    /**
     * Applies the given {@link ProofTreeFilter} to the ProofTree.
     * 
     * @param proofTreeFilter
     *            the filter to apply.
     */
    public void filterBy(final ProofTreeFilter proofTreeFilter) {
        filtersMap.put(proofTreeFilter, true);
        applyFilters();
    }

    /**
     * TODO
     * 
     * @return
     */
    public DataModel getDataModel() {
        return dataModel;
    }

    /**
     * Returns the list of loaded filters.
     * 
     * @return the {@link #filtersMap}.
     */
    public Map<ProofTreeFilter, Boolean> getFiltersMap() {
        return filtersMap;
    }

    /**
     * Returns the activation status for a filter.
     * 
     * @param filter
     *            The filter to check
     * @return true iff the filter is activated
     */
    public boolean getFilterStatus(final ProofTreeFilter filter) {
        return filtersMap.get(filter);
    }

    /**
     * Resets all active filters.
     */
    public final void reinit() {
        filtersMap.forEach((filter, active) -> {
            if (active) {
                filtersMap.put(filter, false);
            }
        });
    }

    /**
     * Stops applying the referenced {@link ProofTreeFilter} to the ProofTree.
     * 
     * @param proofTreeFilter
     *            the filter to stop applying.
     */
    public void stopFilteringBy(final ProofTreeFilter proofTreeFilter) {
        filtersMap.remove(proofTreeFilter);
        applyFilters();
    }

    /**
     * Toggles the activation status for a filter.
     * 
     * @param filter
     *            The filter to change the status of.
     */
    public void toggleFilteringStatus(final ProofTreeFilter filter) {
        final boolean newState = !filtersMap.get(filter);
        filtersMap.put(filter, newState);

        /*
         * Attention this checks conflicts between filters. By this filters
         * cannot be removed anymore from the package. For the future it is
         * planned to develop a dynamic method. This is talked about with
         * Richard Bubel.
         */
        // Begin
        if (filter instanceof FilterHideIntermediate) {
            filtersMap.forEach((mapFilter, active) -> {
                if (active && (mapFilter instanceof FilterHideNonInteractive
                        || mapFilter instanceof FilterHideNonSymbolicExecution)) {
                    filtersMap.put(mapFilter, false);
                }
            });
        }
        else if (filter instanceof FilterHideNonInteractive
                || filter instanceof FilterHideNonSymbolicExecution) {
            filtersMap.forEach((mapFilter, active) -> {
                if (active && mapFilter instanceof FilterHideIntermediate) {
                    filtersMap.put(mapFilter, false);
                }
            });
        }
        // End

        applyFilters();
    }

    /**
     * Applies the filters that are currently set to active.
     */
    private void applyFilters() {

        if (dataModel.getLoadedTreeViewState() != null) {
            dataModel.getLoadedTreeViewState().getTreeItem().filter(
                    // reduces all active filters to one
                    getActiveFilters().stream().reduce(new FilterShowAll(), (firstFilter,
                            secondFilter) -> new FilterCombineAND(firstFilter, secondFilter)));
        }
    }

    /**
     * Returns a list of the currently active filters.
     * 
     * @return A list of the currently active filters.
     */
    private List<ProofTreeFilter> getActiveFilters() {

        final List<ProofTreeFilter> filters = new LinkedList<>();

        filtersMap.forEach((filter, active) -> {
            if (active) {
                filters.add(filter);
            }
        });

        return filters;
    }

    /**
     * Wrapper class used to read filter rules from the file system.
     * 
     * @author Florian Breitfelder
     * @author Stefan Pilot
     *
     */
    @SuppressWarnings("PMD.AtLeastOneConstructor")
    private class reflectionWrapper {

        /**
         * Path where filter classes are stored.
         */
        private static final String FILTER_PATH = "filter/";
        /**
         * Stores the URLs of all filters.
         */
        private transient final List<URL> listOfURLs = new ArrayList<>();
        /**
         * Stores the File Names of all filters.
         */
        private transient final List<String> listOfFileNames = new ArrayList<>();

        /**
         * Retrieves the filters URLs and names if KeY is run from a .jar file.
         * 
         * @param jarFile
         *            the .jar file
         * @return A SimpleImmutableEntry containing a List&lt;URL&gt; and a
         *         List&lt;String&gt;
         * @throws IOException
         *             Rethrow this as a runtime exception.
         */
        @SuppressWarnings("PMD.AvoidInstantiatingObjectsInsideLoops")
        private SimpleImmutableEntry<List<URL>, List<String>> getFilterFilesInJar(final File jarFile)
                throws IOException {
            final JarFile jar = new JarFile(jarFile);
            final Enumeration<JarEntry> entries = jar.entries();
            jar.close();
            while (entries.hasMoreElements()) {
                final String fileName = entries.nextElement().getName();

                if (fileName.matches("(de/uka/ilkd/key/nui/prooftree/filter/).*(.class)")) {
                    listOfURLs.add(new File(fileName).toURI().toURL());
                    listOfFileNames.add(
                            fileName.substring(fileName.lastIndexOf('/') + 1, fileName.length()));
                }
            }
            return new SimpleImmutableEntry<>(listOfURLs, listOfFileNames);
        }

        /**
         * Retrieves the filters URLs and names if KeY is built from scratch
         * (and not to a .jar file)
         * 
         * @return A SimpleImmutableEntry containing a List&lt;URL&gt; and a
         *         List&lt;String&gt;
         * @throws MalformedURLException
         *             Rethrow this as a runtime exception.
         */
        private SimpleImmutableEntry<List<URL>, List<String>> getFilterFilesInIDE()
                throws MalformedURLException {
            // Run with IDE
            // Look for all class files in PATH and store their urls
            final File[] files = new File(getClass().getResource(FILTER_PATH).getPath())
                    .listFiles();
            for (final File file : files) {
                if (file.isFile() && file.getName().matches(".*(.class)")) {
                    final URL urlClassFile = file.toURI().toURL();
                    listOfURLs.add(urlClassFile);
                    listOfFileNames.add(file.getName());
                }
            }
            return new SimpleImmutableEntry<>(listOfURLs, listOfFileNames);
        }

        /**
         * Retrieves the filters URLs and names.
         * 
         * @return A SimpleImmutableEntry containing a List&lt;URL&gt; and a
         *         List&lt;String&gt;
         */
        public SimpleImmutableEntry<List<URL>, List<String>> getFilterFiles() {
            // path of the jar file
            final File jarFile = new File(
                    getClass().getProtectionDomain().getCodeSource().getLocation().getPath());
            try {
                if (jarFile.isFile()) { // Run with JAR file
                    return getFilterFilesInJar(jarFile);
                }
                return getFilterFilesInIDE();
            }
            catch (IOException e) {
                throw new RuntimeException(
                        "An IO Exception occured when trying to load filter rules.", e);
            }
        }
    }

    /**
     * Searches for applicable filters in the package
     * de.uka.ilkd.key.nui.prooftree.filter.
     * 
     * @return A list of filters
     */
    private List<ProofTreeFilter> searchFilterClasses() {

        final SimpleImmutableEntry<List<URL>, List<String>> files = new reflectionWrapper()
                .getFilterFiles();

        final List<ProofTreeFilter> filters = new LinkedList<>();

        // Convert listOfURLs to an array of URLs. This array is needed for
        // the classLoader
        final URL[] urls = files.getKey().toArray(new URL[] {});

        // initialize classLoader
        final URLClassLoader classLoader = new URLClassLoader(urls);

        for (final String fileName : files.getValue()) {
            // build binaryClassName to load class with classLoader
            final String binaryClassName = BIN_NAME_PREFX
                    + fileName.substring(0, fileName.lastIndexOf('.'));

            // Load possible filter class
            try {
                final Class<?> myClass = classLoader.loadClass(binaryClassName);

                // Load annotations of the class
                final Annotation[] annotations = myClass
                        .getAnnotationsByType(FilterAnnotation.class);

                // check if isFilter is true
                for (final Annotation annotation : annotations) {
                    /*
                     * If the annotation isFilter is true, the current class is
                     * a valid filter class therefore create a new instance of
                     * it and add it to filters.
                     */
                    if (((FilterAnnotation) annotation).isFilter()) {
                        filters.add((ProofTreeFilter) myClass.newInstance());
                    }
                }
            }
            catch (ClassNotFoundException | InstantiationException | IllegalAccessException e) {
                e.printStackTrace();
            }
        }
        try {
            classLoader.close();
        }
        catch (IOException e) {
            e.printStackTrace();
        }

        return filters;
    }

}
