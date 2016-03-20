package de.uka.ilkd.key.nui.prooftree;

import java.io.File;
import java.io.IOException;
import java.lang.annotation.Annotation;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
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
     * A map storing filters with their respective activation flag.
     */

    final private Map<ProofTreeFilter, Boolean> filtersMap = Collections
            .synchronizedMap(new ConcurrentHashMap<>());

    /**
     * The data model.
     */
    private final DataModel dataModel;

    /**
     * Path where filter classes are stored.
     */
    static final String FILTER_PATH = "filter/";

    /**
     * Prefix for binary class files.
     */
    static final String BINARY_NAME_PREFIX = "de.uka.ilkd.key.nui.prooftree.filter.";

    /**
     * TODO
     * 
     * @return
     */
    public DataModel getDataModel() {
        return dataModel;
    }

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
     * Searches for applicable filters in the package
     * de.uka.ilkd.key.nui.prooftree.filter.
     * 
     * @return A list of filters
     */
    private List<ProofTreeFilter> searchFilterClasses() {
        final List<ProofTreeFilter> filters = new LinkedList<>();

        // path of the jar file
        final File jarFile = new File(
                getClass().getProtectionDomain().getCodeSource().getLocation().getPath());

        final ArrayList<URL> listOfURLs = new ArrayList<>();
        final ArrayList<String> listOfFileNames = new ArrayList<>();

        if (jarFile.isFile()) { // Run with JAR file
            try (JarFile jar = new JarFile(jarFile)) {
                final Enumeration<JarEntry> entries = jar.entries();
                while (entries.hasMoreElements()) {
                    final String fileName = entries.nextElement().getName();

                    if (fileName.matches("(de/uka/ilkd/key/nui/prooftree/filter/).*(.class)")) {

                        final URL url = new File(fileName).toURI().toURL();
                        listOfURLs.add(url);
                        listOfFileNames.add(fileName.substring(fileName.lastIndexOf('/') + 1,
                                fileName.length()));
                    }
                }
            }
            catch (IOException e) {

                // TODO Auto-generated catch block
                // TODO maybe we should throw a RuntimeException
                e.printStackTrace();
            }
        }
        else {// Run with IDE
              // Look for all class files in PATH and store their urls
            final File[] files = new File(getClass().getResource(FILTER_PATH).getPath())
                    .listFiles();

            for (final File file : files) {
                if (file.isFile() && file.getName().matches(".*(.class)")) {
                    try {
                        final URL urlClassFile = file.toURI().toURL();
                        listOfURLs.add(urlClassFile);
                        listOfFileNames.add(file.getName());
                    }
                    catch (MalformedURLException e) {
                        // TODO Auto-generated catch block
                        // TODO maybe we should throw a RuntimeException
                        e.printStackTrace();
                    }
                }
            }
        }

        // Convert listOfURLs to an array of URLs. This array is needed for the
        // classLoader
        URL[] urls = new URL[listOfURLs.size()];
        urls = listOfURLs.toArray(urls);

        ClassLoader classLoader = null;
        try {
            // initialize classLoader
            classLoader = new URLClassLoader(urls);
            String binaryClassName = null;

            for (final String fileName : listOfFileNames) {
                // build binaryClassName to load class with classLoader
                binaryClassName = BINARY_NAME_PREFIX
                        + fileName.substring(0, fileName.lastIndexOf('.'));

                // Load possible filter class

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
        }
        catch (ClassNotFoundException | InstantiationException | IllegalAccessException e) {
            e.printStackTrace();
        }

        return filters;
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
     * Toggles the activation status for a filter.
     * 
     * @param filter
     *            The filter to change the status of.
     */
    public void toggleFilteringStatus(final ProofTreeFilter filter) {
        final boolean newState = !filtersMap.get(filter);
        filtersMap.put(filter, newState);

        applyFilters();
    }

}
