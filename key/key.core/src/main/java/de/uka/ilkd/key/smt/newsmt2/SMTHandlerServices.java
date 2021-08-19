package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.ReplacementMap.NoIrrelevantLabelsReplacementMap;
import org.key_project.util.Streams;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.ServiceLoader;
import java.util.logging.Handler;

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
     * use {@link #getFreshHandlers(Services, MasterHandler)}</b>
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
     * Get a copy of freshly created {@link SMTHandler}s by cloning the reference
     * handlers. They can be used to translate problems to smt
     *
     * @param services passed on to the handlers for initialisation
     * @param mh passed on to the handlers for initialisation
     * @return a freshly created list of freshly created handlers
     * @throws IOException if the resources cannot be read
     */

    public List<SMTHandler> getFreshHandlers(Services services, MasterHandler mh) throws IOException {

        List<SMTHandler> result = new ArrayList<>();

        for (SMTHandler originalHandler : getOriginalHandlers()) {
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
