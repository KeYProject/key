/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import org.jspecify.annotations.NonNull;
import org.key_project.util.Streams;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

/**
 * This class provides some infrastructure to the smt translation process.
 * <p>
 * In particular, it collects the preamble and the snippets for the handlers such that they need not
 * be read from disk multiple times.
 * <p>
 * This class is a singleton.
 *
 * @author Mattias Ulbrich
 * @author Alicia Appelhagen (load handlers from handler names array instead of ServiceLoader)
 */
public class IsabelleHandlerServices {

    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleHandlerServices.class);

    /**
     * A .txt file containing a default handler list to load via
     * {@link #getTemplateHandlers(String[])} if that method's parameter is an empty handlerNames
     * array.
     */
    private static final String DEFAULT_HANDLERS = "defaultHandlers.txt";

    /**
     * Singleton instance
     */
    private static IsabelleHandlerServices theInstance;

    /**
     * A map from template handler objects to their smt2 snippets.
     * <p>
     * Before removing the ServiceLoader from #getOriginalHandlers, an IdentityHashMap was used
     * here. Since the removal of the ServiceLoader leads to snippetMap being modified even after
     * creation, concurrent modification by different solver threads becomes possible. Hence, either
     * every access to snippetMap needs to be synchronized or it needs to be a ConcurrentHashMap -
     * which is not an IdentityHashMap anymore. This should not be a problem as the SMTHandlers
     * don't override equals().
     */
    private final Map<IsabelleHandler, Properties> snippetMap = new ConcurrentHashMap<>();

    // preamble is volatile since sonarcube tells me the synchronisation scheme
    // for loading would be broken otherwise. (MU 2021)
    /**
     * The smt2 preamble
     */
    private volatile String preamble;

    /**
     * lock for synchronisation
     */
    private final Object handlerModificationLock = new Object();

    /**
     * Get the instance of this singleton.
     *
     * @return non-null instance of this class. Always the same.
     */
    public static IsabelleHandlerServices getInstance() {
        if (theInstance == null) {
            theInstance = new IsabelleHandlerServices();
        }
        return theInstance;
    }

    /**
     * Load the original/template SMTHandler instances (from the snippetMap) of all handlers
     * specified as arguments. Add fresh handlers to the snippetMap and load the snippets that
     * belong to these instances if that has not happened yet for any object of a given handler
     * class.
     *
     * <strong>Caution: Do not call this method too often since it may add to the static map of
     * instances to snippets.</strong>
     * <p>
     * It would be a good idea to call this method (at most) once for each solver type with a custom
     * array of handler names.
     * <p>
     * An empty handlerNames list leads to the usage of the handlers defined by defaultHandlers.txt.
     *
     * @param handlerNames a non-null list of non-null strings with class names (s. above)
     * @return a fresh collection containing only the original SMTHandlers from the snippetMap's key
     * set that match the given handler names. The collection's order matches that of the
     * names as well.
     * @throws IOException if loading the snippet Properties for a handler class fails
     */
    public Collection<IsabelleHandler> getTemplateHandlers(String[] handlerNames) throws IOException {
        // If handlerNames is empty, use default handlerNames list.
        if (handlerNames.length == 0) {
            InputStream stream = IsabelleHandlerServices.class.getResourceAsStream(DEFAULT_HANDLERS);
            BufferedReader reader =
                    new BufferedReader(new InputStreamReader(stream, StandardCharsets.UTF_8));
            handlerNames = reader.lines().toArray(String[]::new);
        }
        Collection<IsabelleHandler> result = new LinkedList<>();
        for (String name : handlerNames) {
            try {
                Class<IsabelleHandler> handlerClass = (Class<IsabelleHandler>) Class.forName(name);
                if (findHandler(handlerClass, result)) {
                    continue;
                }
                synchronized (handlerModificationLock) {
                    /*
                     * Make sure that each handler is added to the template handlers (keyset of
                     * snippetMap) at most once and that every thread waits for the result. Also,
                     * every search access on smtProperties should be synchronized in order to avoid
                     * concurrent modification.
                     */
                    if (!findHandler(handlerClass, result)) {
                        IsabelleHandler handler = handlerClass.getConstructor().newInstance();
                        result.add(handler);
                        Properties handlerSnippets = loadSnippets(handlerClass);
                        if (handlerSnippets != null) {
                            snippetMap.put(handler, handlerSnippets);
                        }
                    }
                }
            } catch (ClassNotFoundException e) {
                LOGGER.warn(String.format("Could not load IsabelleHandler:%s%s", System.lineSeparator(),
                        e.getMessage()));
            } catch (NoSuchMethodException | InvocationTargetException | InstantiationException
                     | IllegalAccessException e) {
                LOGGER.warn(String.format("Could not create IsabelleHandler:%s%s",
                        System.lineSeparator(), e.getMessage()));
            }
        }
        // TODO make sure that the order of handlers in result is the same as the order
        // of their names in the name array
        return result;
    }

    // Search for a handler of the given class in the snippetMap and if it exists, add it to
    // the result collection.
    private boolean findHandler(Class<IsabelleHandler> clazz, Collection<IsabelleHandler> result) {
        Optional<IsabelleHandler> handler =
                snippetMap.keySet().stream().filter(h -> h.getClass().equals(clazz)).findFirst();
        if (handler.isPresent()) {
            if (!result.contains(handler.get())) {
                result.add(handler.get());
            }
            return true;
        }
        return false;
    }

    /**
     * Get a copy of freshly created {@link IsabelleHandler}s by cloning the reference handlers. They can
     * be used to translate problems to SMT.
     *
     * @param services       passed on to the handlers for initialisation
     * @param handlerNames   the fully classified class names of the SMTHandlers to be used If this is
     *                       empty or null, all existing handlers will be used.
     * @param handlerOptions arbitrary String options for the SMTHandlers
     * @param mh             passed on to the handlers for initialisation
     * @return a freshly created list of freshly created handlers
     * @throws IOException if the resources cannot be read
     */

    public List<IsabelleHandler> getFreshHandlers(Services services, @NonNull String[] handlerNames,
                                                  String[] handlerOptions, IsabelleMasterHandler mh) throws IOException {

        List<IsabelleHandler> result = new ArrayList<>();

        // Possibly problematic: snippetMap may be modified by another thread while
        // calling snippetMap.get(handler)
        // -> concurrent modification?
        for (IsabelleHandler handler : getTemplateHandlers(handlerNames)) {
            // After getOriginalHandlers(handlerNames), snippets for all handlers are
            try {
                IsabelleHandler copy = handler.getClass().getConstructor().newInstance();
                /*
                 * Either use that synchronized block or make snippetMap a ConcurrentHashMap:
                 * Properties snippet; synchronized (handlerModificationLock) { // Avoid concurrent
                 * modification of the snippetMap while accessing it. snippet =
                 * snippetMap.get(handler); }
                 */
                copy.init(mh, services, snippetMap.get(handler), handlerOptions);
                result.add(copy);
            } catch (Exception e) {
                throw new IOException(e);
            }
        }

        return result;
    }

    /**
     * Look up the resource for the snippets of a particular smt handler class. They must be in the
     * same package and have the name of the class with ".preamble.xml" attached.
     *
     * @param aClass class reference for localisation
     * @return freshly created property object, null if the resource does not exist
     * @throws IOException may be thrown during reading of the resource
     */
    private static Properties loadSnippets(Class<?> aClass) throws IOException {
        String resourceName = aClass.getSimpleName() + ".preamble.xml";
        URL resource = aClass.getResource(resourceName);
        if (resource != null) {
            Properties snippets = new Properties();
            try (InputStream is = resource.openStream()) {
                snippets.loadFromXML(is);
            }
            return snippets;
        }
        return null;
    }

    /**
     * There is a fixed SMT2lib preamble first sent to the solver.
     * <p>
     * Get this preamble.
     *
     * @return a non-null string, always the same
     */
    public String getPreamble() {
        try {
            if (preamble == null) {
                synchronized (handlerModificationLock) {
                    if (preamble == null) {
                        // make sure this is only ever read once and everyone
                        // waits for it.
                        preamble = Streams.toString(
                                IsabelleHandlerServices.class.getResourceAsStream("preamble.smt2"));
                    }
                }
            }
            return preamble;
        } catch (IOException e) {
            // the caller cannot really deal with exceptions ...
            throw new RuntimeException(e);
        }
    }
}