/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.io;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import recoder.AbstractService;
import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.bytecode.ByteCodeParser;
import recoder.bytecode.ClassFile;
import recoder.convenience.Naming;
import recoder.service.ErrorHandler;
import recoder.util.Debug;

/**
 * @author RN
 * @author AL
 */
public class DefaultClassFileRepository extends AbstractService
        implements ClassFileRepository, PropertyChangeListener {

    // private PathList searchPath;
    private final Map<String, ClassFile> classname2cf = new HashMap<>(64);

    private final ByteCodeParser bytecodeParser = new ByteCodeParser();

    /**
     * Cached search path list.
     */
    private PathList searchPathList;

    /**
     * @param config the configuration this services becomes part of.
     */
    public DefaultClassFileRepository(ServiceConfiguration config) {
        super(config);
    }

    public void initialize(ServiceConfiguration cfg) {
        super.initialize(cfg);
        ProjectSettings settings = cfg.getProjectSettings();
        settings.addPropertyChangeListener(this);
        searchPathList = settings.getSearchPathList();
    }

    protected final PathList getSearchPathList() {
        return searchPathList;
    }

    ErrorHandler getErrorHandler() {
        return serviceConfiguration.getProjectSettings().getErrorHandler();
    }

    public void propertyChange(PropertyChangeEvent evt) {
        String changedProp = evt.getPropertyName();
        if (changedProp.equals(PropertyNames.INPUT_PATH)) {

            // should check for admissibility of the new path
            // if it has been added only, there is nothing to do
            // otherwise, for all class types check if the location
            // would have changed; if so, invalidate them
            searchPathList = serviceConfiguration.getProjectSettings().getSearchPathList();
        }
    }

    /**
     * Searches for the location of the class file for the given class.
     *
     * @param classname the name of the class for which the class file should be looked up.
     */
    public DataLocation findClassFile(String classname) {
        return getSearchPathList().find(Naming.dot(Naming.makeFilename(classname), "class"));
    }

    public ClassFile getClassFile(String classname) {
        ClassFile result = classname2cf.get(classname);
        if (result != null) {
            return result;
        }
        DataLocation loc = findClassFile(classname);
        if (loc == null) {
            String innername = classname;
            int ldp = innername.length() - 1;
            StringBuilder sb = new StringBuilder(innername);
            while (true) {
                ldp = innername.lastIndexOf('.', ldp);
                if (ldp == -1) {
                    return null;
                }
                sb.setCharAt(ldp, '$');
                innername = sb.toString();
                result = classname2cf.get(innername);
                if (result != null) {
                    return result;
                }
                loc = findClassFile(innername);
                if (loc != null) {
                    classname = innername;
                    break;
                }
            }
        }
        try {
            InputStream is = loc.getInputStream();
            Debug.assertNonnull(is, "No input stream for data location");
            bytecodeParser.readJava5Signatures =
                serviceConfiguration.getProjectSettings().java5Allowed();
            result = bytecodeParser.parseClassFile(is, loc.toString());
            is.close();
            loc.inputStreamClosed();
            // result.setLocation(loc.toString());
            classname2cf.put(classname, result);
        } catch (IOException | ParserException e) {
            getErrorHandler().reportError(e);
            result = null;
        }
        return result;
    }

    public List<ClassFile> getKnownClassFiles() {
        int n = classname2cf.size();
        List<ClassFile> res = new ArrayList<>(n);
        for (ClassFile cf : classname2cf.values()) {
            res.add(cf);
        }
        return res;
    }

    public String information() {
        return "" + classname2cf.size() + " class files";
    }

}
