package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import org.key_project.util.Streams;

import javax.annotation.Nullable;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.ServiceLoader;

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

    /** The name of the package where this class resides. Used for
     * prefixing when loading handlers.
     */
    private static final String PACKAGE_PREFIX =
            SMTHandlerServices.class.getPackageName() + ".";

    /** Singleton instance */
    private static SMTHandlerServices theInstance;

    /** The list of instantiated available handlers */
    private List<SMTHandler> handlers;

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
     * Get a list of all handlers available in the system.
     *
     * <b>Do not use this list directly, but
     * use {@link #getFreshHandlers(Services, List, MasterHandler)}</b>
     * if you intend to initialise them and run them.
     *
     * @return always the same list of {@link SMTHandler}s, not null
     * @throws IOException if the resources cannot be read
     */
    public List<SMTHandler> getOriginalHandlers() throws IOException {
        if(handlers != null) {
            return handlers;
        }

        synchronized (theCreationLock) {
            // Make sure that there is at most one invocation of makeHandlers,
            // and that everyone waits for the result.
            if(handlers != null) {
                return handlers;
            }
            this.handlers = makeHandlers();
            return this.handlers;
        }
    }

    /**
     * Load all handlers using a service loader. Load the snippets that belong
     * to them.
     * @return an unmodifiable view on a freshly created list
     * @throws IOException if the resources cannot be read
     */
    private List<SMTHandler> makeHandlers() throws IOException {
        List<SMTHandler> result = new ArrayList<>();
        for (SMTHandler smtHandler : ServiceLoader.load(SMTHandler.class)) {
            Properties handlerSnippets = loadSnippets(smtHandler.getClass());
            if (handlerSnippets != null) {
                snippetMap.put(smtHandler,  handlerSnippets);
            }
            smtProperties.addAll(smtHandler.getProperties());
            result.add(smtHandler);
        }
        return Collections.unmodifiableList(result);
    }

    /**
     * Loadd all handlers specified as arguments. Load the snippets that belong
     * to these instances. This can be used if a translation does not want to
     * use the standard array of handlers.
     *
     * <strong>Caution: Do not call this method too often since it adds to the
     * static map of instances to snippets.</strong>
     *
     * It would be a good idea to call this method (at most) once for each
     * solver type with a custom array of handlers.
     *
     * The strings in the argument can either be fully qualified class names
     * or class names package. In the latter case the prefix for this package
     * here will be added.
     *
     * @param classNames a non-null list of non-null strings with classnames (s. above)
     *
     * @return a fresh array of freshly created handlers.
     */
    public List<SMTHandler> makeHandlers(Collection<String> classNames) throws IOException {
        List<SMTHandler> result = new ArrayList<>();
        for (String className : classNames) {
            if (!className.contains(".")) {
                className = PACKAGE_PREFIX + className;
            }
            try {
                SMTHandler smtHandler = (SMTHandler) Class.forName(className).getConstructor().newInstance();
                result.add(smtHandler);
            } catch (Exception e) {
                throw new IOException("Cannot instantiate SMTHandler " + className, e);
            }
        }

        for (SMTHandler smtHandler : result) {
            Properties handlerSnippets = loadSnippets(smtHandler.getClass());
            if (handlerSnippets != null) {
                snippetMap.put(smtHandler,  handlerSnippets);
            }
            smtProperties.addAll(smtHandler.getProperties());
        }

        return result;
    }

    /**
     * Get a copy of freshly created {@link SMTHandler}s by cloning the reference
     * handlers. They can be used to translate problems to smt
     *
     * If null is specified for the smt handlers, the default list is used.
     *
     * <strong>Important: The list of handlers to be copied must have been created
     * by this services object. Otherwise the properties will not be correctly
     * populated.</strong>
     *
     * @param services passed on to the handlers for initialisation
     * @param smtHandlers either null or a set of smt handlers to be copied.
     * @param mh passed on to the handlers for initialisation
     * @return a freshly created list of freshly created handlers
     * @throws IOException if the resources cannot be read
     */

    public List<SMTHandler> getFreshHandlers(Services services, @Nullable List<SMTHandler> smtHandlers, MasterHandler mh) throws IOException {

        List<SMTHandler> result = new ArrayList<>();

        if (smtHandlers == null) {
            smtHandlers = getOriginalHandlers();
        }

        for (SMTHandler originalHandler : smtHandlers) {
            try {
                SMTHandler copy = originalHandler.getClass().getConstructor().newInstance();
                copy.init(mh, services, snippetMap.get(originalHandler));
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
        getOriginalHandlers();
        return Collections.unmodifiableCollection(smtProperties);
    }
}
