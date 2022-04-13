package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import org.key_project.util.Streams;
import org.slf4j.LoggerFactory;
import org.slf4j.Logger;

import javax.annotation.Nullable;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.util.*;
import java.util.stream.Collectors;

/**
 * This class provides some infrastructure to the smt translation proceess.
 *
 * In particular, it collects the preamble and the snippets for the handlers
 * such that they need not be read from disk multiple times.
 *
 * This class is a singleton.
 *
 * @author Mattias Ulbrich
 */
public class SMTHandlerServices {

    private static final Logger LOGGER = LoggerFactory.getLogger(SMTHandlerServices.class);

    /** The name of the package where this class resides. Used for
     * prefixing when loading handlers.
     */
    private static final String PACKAGE_PREFIX =
            SMTHandlerServices.class.getPackageName() + ".";

    /** Singleton instance */
    private static SMTHandlerServices theInstance;

    /** The list of instantiated available handlers */
    private List<SMTHandler> handlers = new ArrayList<>();

    /** A map from handler to their smt2 snippets */
    private final Map<SMTHandler, Properties> snippetMap = new IdentityHashMap<>();

    // preamble is volatile since sonarcube tells me the synchronisation scheme
    // for loading would be broken otherwise. (MU 2021)
    /** The smt2 preamble */
    private volatile String preamble;

    /** lock for synchronisation */
    private final Object theCreationLock = new Object();

    /** A collection of the properties */
    private List<SMTHandlerProperty<?>> smtProperties = makeBuiltinProperties();

    /**
     * Get the instance of this singleton.
     *
     * @return non-null instance of this class. Always the same.
     */
    public static SMTHandlerServices getInstance() {
        if (theInstance == null) {
            theInstance = new SMTHandlerServices();
        }
        return theInstance;
    }

    /**
     * Load the original SMTHandler instances (from the snippetMap) of all handlers
     * specified as arguments.
     * Add fresh handlers to the snippetMap and load the snippets that belong to these instances
     * if that has not happened yet for any object of a given handler class.
     *
     * <strong>Caution: Do not call this method too often since it may add to the
     * static map of instances to snippets.</strong>
     *
     * It would be a good idea to call this method (at most) once for each
     * solver type with a custom array of handler names.
     *
     * @param handlerNames a non-null list of non-null strings with class names (s. above)
     *
     * @return a fresh collection containing only the original SMTHandlers from the
     *              snippetMap's key set that match the given handler names.
     *              The collection's order matches that of the names as well.
     *
     */
    private Collection<SMTHandler> getOriginalHandlers(String[] handlerNames) throws IOException {
        Collection<SMTHandler> result = new LinkedList<>();
        for (String name : handlerNames) {
            try {
                Class<SMTHandler> handlerClass = (Class<SMTHandler>) Class.forName(name);
                if (findHandler(handlerClass, result)) {
                    continue;
                }
                synchronized (theCreationLock) {
                    // Make sure that each handler is added to the handler list at most once
                    // and that everyone waits for the result.
                    if (findHandler(handlerClass, result)) {
                        continue;
                    }
                    SMTHandler handler = handlerClass.getConstructor().newInstance();
                    handlers.add(handler);
                    result.add(handler);
                    Properties handlerSnippets = loadSnippets(handlerClass);
                    if (handlerSnippets != null) {
                        snippetMap.put(handler, handlerSnippets);
                    }
                    smtProperties.addAll(handler.getProperties());
                }
            } catch (ClassNotFoundException e) {
                LOGGER.warn("Could not load SMTHandler:" + System.lineSeparator()
                        + e.getMessage());
                continue;
            } catch (NoSuchMethodException | InvocationTargetException
                    | InstantiationException | IllegalAccessException e) {
                LOGGER.warn("Could not create SMTHandler:" + System.lineSeparator()
                        + e.getMessage());
                continue;
            }
        }
        // TODO make sure that the order of handlers in result is the same as the order
        //  of their names in the name array
        return result;
    }

    private boolean findHandler(Class<SMTHandler> clazz, Collection<SMTHandler> result) {
        Optional<SMTHandler> handler = handlers.stream()
                .filter(h -> h.getClass().equals(clazz)).findFirst();
        if (handler.isPresent()) {
            if (!result.contains(handler)) {
                result.add(handler.get());
            }
            return true;
        }
        return false;
    }

    /**
     * Get a copy of freshly created {@link SMTHandler}s by cloning the reference
     * handlers. They can be used to translate problems to SMT.
     *
     * @param services passed on to the handlers for initialisation
     * @param handlerNames the fully classified class names of the SMTHandlers to be used
     *                     If this is empty or null, all existing handlers will be used.
     * @param handlerOptions arbitrary String options for the SMTHandlers
     * @param mh passed on to the handlers for initialisation
     * @return a freshly created list of freshly created handlers
     * @throws IOException if the resources cannot be read
     */

    public List<SMTHandler> getFreshHandlers(Services services, @Nullable String[] handlerNames,
                                             String[] handlerOptions, MasterHandler mh)
            throws IOException {

        List<SMTHandler> result = new ArrayList<>();

        for (SMTHandler handler : getOriginalHandlers(handlerNames)) {
            try {
                // TODO SMTHandler#copy() would be nice(?)
                SMTHandler copy = handler.getClass().getConstructor().newInstance();
                copy.init(mh, services, snippetMap.get(handler), handlerOptions);
                result.add(copy);
            } catch (Exception e) {
                throw new IOException(e);
            }
        }

        return result;
    }

    /**
     * Look up the resource for the snippets of a particular smt handler class.
     * They must be in the same package and have the name of the class with
     * ".preamble.xml" attached.
     *
     * @param aClass class reference for localisation
     * @return freshly created property object, null if the resource does not
     * exist
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
     *
     * Get this preamble.
     *
     * @return a non-null string, always the same
     */
    public String getPreamble() {
        try {
            if (preamble == null) {
                synchronized (theCreationLock) {
                    if(preamble == null) {
                        // make sure this is only ever read once and everyone
                        // waits for it.
                        preamble = Streams.toString(
                                SMTHandlerServices.class.
                                        getResourceAsStream("preamble.smt2"));
                    }
                }
            }
            return preamble;
        } catch (IOException e) {
            // the caller cannot really deal with exceptions ...
            throw new RuntimeException(e);
        }
    }

    private List<SMTHandlerProperty<?>> makeBuiltinProperties() {
        List<SMTHandlerProperty<?>> result = new ArrayList<>();
        result.addAll(HandlerUtil.GLOBAL_PROPERTIES);
        return result;
    }

    /**
     * Get the list of all {@link SMTHandlerProperty}s known in the system
     *
     * @return an unmodifiable view on the smt properties, not null
     * @throws IOException if resources cannot be read
     */
    public Collection<SMTHandlerProperty<?>> getSMTProperties() throws IOException {
        // trigger the translation ...
        //getOriginalHandlers();
        return Collections.unmodifiableCollection(smtProperties);
    }
}
