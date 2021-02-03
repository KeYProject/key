package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import org.key_project.util.Streams;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.ServiceLoader;

public class SMTHandlerServices {

    private static SMTHandlerServices theInstance;
    private List<SMTHandler> handlers;
    private Map<SMTHandler, Properties> snippetMap = new IdentityHashMap<>();
    private String preamble;
    private Object theCreationLock = new Object();

    public static SMTHandlerServices getInstance() {
        if (theInstance == null) {
            theInstance = new SMTHandlerServices();
        }
        return theInstance;
    }
    
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

    private List<SMTHandler> makeHandlers() throws IOException {
        List<SMTHandler> result = new ArrayList<>();
        for (SMTHandler smtHandler : ServiceLoader.load(SMTHandler.class)) {
            Properties handlerSnippets = loadSnippets(smtHandler.getClass());
            if (handlerSnippets != null) {
                snippetMap.put(smtHandler,  handlerSnippets);
            }
            result.add(smtHandler);
        }
        return result;
    }

    public List<SMTHandler> getFreshHandlers(Services services, MasterHandler mh) throws IOException {

        List<SMTHandler> result = new ArrayList<>();

        for (SMTHandler originalHandler : getOriginalHandlers()) {
            try {
                SMTHandler copy = originalHandler.getClass().newInstance();
                copy.init(mh, services, snippetMap.get(originalHandler));
                result.add(copy);
            } catch (Exception e) {
                throw new IOException(e);
            }
        }

        return result;
    }

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

    public String getPreamble() {
        try {
            if(preamble == null) {
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

}
