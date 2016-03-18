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
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Observable;
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
     * A map storing filters with their resp. activation flag.
     */
    final private Map<ProofTreeFilter, Boolean> filtersMap = Collections
            .synchronizedMap(new LinkedHashMap<>());

    /**
     * The data model.
     */
    final private DataModel dm;

    // TODO stores the current tree. When the model class provides a
    // funtion to get the current tree this can be deleted.
    private String currentTree;

    /**
     * Constructor.
     * 
     * @param model
     *            The DataModel.
     */
    public FilteringHandler(final DataModel model) {
        System.out.println("Konstruktor FilteringHandler");
        this.dm = model;

        final List<ProofTreeFilter> filters = searchFilterClasses();
        filters.forEach((filter) -> filtersMap.put(filter, false));

        model.addObserver((final Observable obs, final Object arg) -> {
            currentTree = (String) arg;
            reinit();
        });
    }

    /**
     * Resets all active filters.
     */
    public void reinit() {
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
        System.out.println("Start searchFilterClasses()");
        final List<ProofTreeFilter> filters = new LinkedList<ProofTreeFilter>();

        // Path were filter class's are stored
        final String PATH = "filter/";
        // Prefix for binary class names
        final String BINARY_NAME_PREFIX = "de.uka.ilkd.key.nui.prooftree.filter.";
        // path of the jar file
        final File jarFile = new File(getClass().getProtectionDomain()
                .getCodeSource().getLocation().getPath());

        ArrayList<URL> listOfURLs = new ArrayList<URL>();
        ArrayList<String> listOfFileNames = new ArrayList<String>();

        if (jarFile.isFile()) { // Run with JAR file
            System.out.println("Run with JAR file");
            try (JarFile jar = new JarFile(jarFile)) {
                final Enumeration<JarEntry> entries = jar.entries();
                System.out.println("Entrie: "+entries.toString()+" More?= "+ entries.hasMoreElements());
                while (entries.hasMoreElements()) {
                    final String fileName = entries.nextElement().getName();
                    if (fileName.matches(
                            "(de/uka/ilkd/key/nui/prooftree/filter/).*(.class)")) {
                        URL url = new File(fileName).toURI().toURL();
                        System.out.println(url.toString());
                        listOfURLs.add(url);
                        listOfFileNames.add(fileName.substring(
                                fileName.lastIndexOf("/") + 1,
                                fileName.length()));
                    }
                }
            }
            catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
        else {// Run with IDE
              // Look for all class files in PATH and store their urls
            File[] files = new File(getClass().getResource(PATH).getPath())
                    .listFiles();

            for (File file : files) {
                if (file.isFile() && file.getName().matches(".*(.class)")) {
                    try {
                        URL urlClassFile = file.toURI().toURL();
                        listOfURLs.add(urlClassFile);
                        listOfFileNames.add(file.getName());
                    }
                    catch (MalformedURLException e) {
                        // TODO Auto-generated catch block
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

            for (String fileName : listOfFileNames) {
                // build binaryClassName to load class with classLoader
                binaryClassName = BINARY_NAME_PREFIX
                        + fileName.substring(0, fileName.lastIndexOf("."));

                // Load possible filter class
                Class<?> c = classLoader.loadClass(binaryClassName);
                // Load annotations of the class
                Annotation[] annotations = c.getAnnotations();
                // if the class has no annotations it cannot be a filter class
                if (annotations == null) {
                    continue;
                }
                else {
                    for (Annotation annotation : annotations) {
                        // Check if there is a annotations of type
                        // FilterAnnotation
                        if (annotation instanceof FilterAnnotation) {
                            FilterAnnotation filterAnnotation = (FilterAnnotation) annotation;
                            /*
                             * If the annotation isFilter is true, the current
                             * class is a valid filter class therefore create a
                             * new instance of it and add it to filters.
                             */
                            if (filterAnnotation.isFilter()) {
                                System.out.println(
                                        "Added Filter: " + c.getName());
                                filters.add((ProofTreeFilter) c.newInstance());
                            }
                        }
                    }
                }

            }
        }
        catch (ClassNotFoundException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        catch (InstantiationException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        catch (IllegalAccessException e) {
            // TODO Auto-generated catch block
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

        final List<ProofTreeFilter> filters = new LinkedList<ProofTreeFilter>();

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
        final List<ProofTreeFilter> activeFilters = getActiveFilters();

        // reduces all active filers to one
        final ProofTreeFilter redFilter = activeFilters.stream()
                .reduce(new FilterShowAll(), (f1, f2) -> {
                    return new FilterCombineAND(f1, f2);
                });

        final ProofTreeItem root = dm.getTreeViewState(currentTree)
                .getTreeItem();
        root.filter(redFilter);
    }

    /**
     * @return the filtersMap
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
