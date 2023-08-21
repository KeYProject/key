/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.io;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.*;
import java.util.*;

import recoder.AbstractService;
import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.convenience.Naming;
import recoder.java.*;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.PackageReference;
import recoder.service.*;
import recoder.util.Debug;
import recoder.util.ProgressListener;
import recoder.util.ProgressListenerManager;

/**
 * @author RN
 * @author AL
 */
public class DefaultSourceFileRepository extends AbstractService
        implements SourceFileRepository, ChangeHistoryListener, PropertyChangeListener {

    public final static FilenameFilter JAVA_FILENAME_FILTER = (dir, name) -> name.endsWith(".java");
    private final static boolean DEBUG = false;
    /**
     * Cache: data location to compilation units.
     */
    private final Map<DataLocation, CompilationUnit> location2cu =
        new HashMap<>();
    /**
     * Set of units that have been changed and have to be rewritten.
     */
    private final Set<CompilationUnit> changedUnits = new HashSet<>();
    /**
     * Set of units that are obsolete and should be deleted.
     */
    private final Set<DataLocation> deleteUnits = new HashSet<>();
    /**
     * Progress listener management.
     */
    final ProgressListenerManager listeners = new ProgressListenerManager(this);
    /**
     * The change history service.
     */
    private ChangeHistory changeHistory;
    /**
     * Cached search path list.
     */
    private PathList searchPathList;
    /**
     * Cached output path.
     */
    private File outputPath;

    /**
     * @param config the configuration this services becomes part of.
     */
    public DefaultSourceFileRepository(ServiceConfiguration config) {
        super(config);
    }

    public void initialize(ServiceConfiguration cfg) {
        super.initialize(cfg);
        changeHistory = cfg.getChangeHistory();
        changeHistory.addChangeHistoryListener(this);
        ProjectSettings settings = cfg.getProjectSettings();
        settings.addPropertyChangeListener(this);
        searchPathList = settings.getSearchPathList();
        outputPath = new File(settings.getProperty(PropertyNames.OUTPUT_PATH));
    }

    protected final PathList getSearchPathList() {
        return searchPathList;
    }

    protected final File getOutputPath() {
        return outputPath;
    }

    public void addProgressListener(ProgressListener l) {
        listeners.addProgressListener(l);
    }

    public void removeProgressListener(ProgressListener l) {
        listeners.removeProgressListener(l);
    }

    public void propertyChange(PropertyChangeEvent evt) {
        String changedProp = evt.getPropertyName();
        if (changedProp.equals(ProjectSettings.INPUT_PATH)) {
            // should check for admissibility of the new path
            // if it has been added only, there is nothing to do
            // otherwise, for all class types check if the location
            // would have changed; if so, invalidate them
            searchPathList = serviceConfiguration.getProjectSettings().getSearchPathList();
        } else if (changedProp.equals(ProjectSettings.OUTPUT_PATH)) {
            outputPath = new File(
                serviceConfiguration.getProjectSettings().getProperty(ProjectSettings.OUTPUT_PATH));
        }
    }

    // remove cu from repository
    private void deregister(CompilationUnit cu) {
        DataLocation loc = cu.getDataLocation();
        if (loc != null) {
            if (location2cu.get(loc) == cu) {
                location2cu.remove(loc);
                changedUnits.remove(cu); // no need to write it back
                if (DEBUG) {
                    Debug.log("Deregistering " + loc);
                }
                DataLocation orig = cu.getOriginalDataLocation();
                if (!loc.equals(orig)) {
                    // remove it except when from original location
                    deleteUnits.add(loc);
                }
            }
        }
    }

    // add cu to repository
    private void register(CompilationUnit cu) {
        DataLocation loc = cu.getDataLocation();
        if (loc == null) {
            changedUnits.add(cu); // assume the file is not up to date
            loc = createDataLocation(cu);
            cu.setDataLocation(loc);
        }
        if (location2cu.get(loc) != cu) {
            if (DEBUG) {
                Debug.log("Registering " + loc);
            }
            deleteUnits.remove(loc);
            location2cu.put(loc, cu);
        }
    }

    // check if the given program element can influence on the canonical
    // name of the compilation unit
    private boolean isPartOfUnitName(ProgramElement pe) {
        if (pe instanceof Identifier || pe instanceof PackageReference) {
            return isPartOfUnitName(pe.getASTParent());
        }
        if (pe instanceof PackageSpecification) {
            return true;
        }
        if (pe instanceof TypeDeclaration) {
            NonTerminalProgramElement parent = pe.getASTParent();
            return (parent instanceof CompilationUnit)
                    && (((CompilationUnit) parent).getPrimaryTypeDeclaration() == pe);
        }
        return false;
    }

    // possible optimization: react on replacements
    public void modelChanged(ChangeHistoryEvent changes) {
        List<TreeChange> changed = changes.getChanges();
        for (int i = changed.size() - 1; i >= 0; i -= 1) {
            TreeChange tc = changed.get(i);
            ProgramElement pe = tc.getChangeRoot();
            CompilationUnit cu = tc.getCompilationUnit();
            if (pe == cu) {
                if (tc instanceof AttachChange) {
                    register(cu);
                } else if (tc instanceof DetachChange) {
                    deregister(cu);
                }
            } else {
                if (isPartOfUnitName(pe)) {
                    // re-register under new location
                    DataLocation loc = cu.getDataLocation(); // old location
                    DataLocation loc2 = createDataLocation(cu); // new location
                    if (!loc.equals(loc2)) {
                        deregister(cu);
                        cu.setDataLocation(loc2);
                        register(cu);
                    }
                }
                changedUnits.add(cu);
            }
            if (cu == null) {
                Debug.log("Null Unit changed in " + tc);
            }
        }
    }

    /**
     * Searches for the location of the source file for the given class.
     *
     * @param classname the name of the class for which the source file should be looked up.
     */
    public DataLocation findSourceFile(String classname) {
        // possible optimzation: cache it !!!
        String file = Naming.dot(Naming.makeFilename(classname), "java");
        return getSearchPathList().find(file);
    }

    protected CompilationUnit getCompilationUnitFromLocation(DataLocation loc)
            throws ParserException {
        Debug.assertNonnull(loc, "Null location for compilation unit");
        CompilationUnit result = location2cu.get(loc);
        if (result != null) {
            return result;
        }
        // ok - lets parse the sources
        try {
            Reader in;
            if (!loc.hasReaderSupport() || (in = loc.getReader()) == null) {
                Debug.error("Location of source file provides no reader");
                return null;
            }
            result = serviceConfiguration.getProgramFactory().parseCompilationUnit(in);
            in.close();
            loc.readerClosed();
            result.setDataLocation(loc);
            location2cu.put(loc, result); // let this be done by the history
            changeHistory.attached(result);
        } catch (IOException e) {
            Debug.error("Exception while reading from input stream: " + e);
        } catch (ParserException pe) {
            Debug.error("Exception while parsing unit " + loc);
            throw pe;
        }
        return result;
    }

    public CompilationUnit getCompilationUnitFromFile(String filename) throws ParserException {
        Debug.assertNonnull(filename);
        File f = new File(filename);
        DataLocation loc = null;
        if (f.isFile() && f.isAbsolute()) {
            String newfilename = getSearchPathList().getRelativeName(filename);
            if (newfilename.equals(filename)) {
                // not part of the regular search path; load anyway...
                loc = new DataFileLocation(f);
            } else {
                loc = getSearchPathList().find(newfilename);
            }
        } else {
            loc = getSearchPathList().find(filename);
            // System.err.println("Location for " + filename +": " + loc);
        }
        return loc != null ? getCompilationUnitFromLocation(loc) : null;
    }

    public List<CompilationUnit> getCompilationUnitsFromFiles(String[] filenames)
            throws ParserException {
        Debug.assertNonnull(filenames);
        List<CompilationUnit> res = new ArrayList<>();
        listeners.fireProgressEvent(0, filenames.length, "Importing Source Files");
        for (int i = 0; i < filenames.length; i += 1) {
            listeners.fireProgressEvent(i,
                "Parsing " + filenames[i]);
            CompilationUnit cu = getCompilationUnitFromFile(filenames[i]);
            if (cu != null) {
                res.add(cu);
            }
        }
        listeners.fireProgressEvent(filenames.length);
        return res;
    }

    public CompilationUnit getCompilationUnit(String classname) {
        DataLocation loc = findSourceFile(classname);
        if (loc == null || loc instanceof ArchiveDataLocation) {
            return null;
        }
        try {
            return getCompilationUnitFromLocation(loc);
        } catch (ParserException pe) {
            serviceConfiguration.getProjectSettings().getErrorHandler().reportError(pe);
            return null;
        }
    }

    public List<CompilationUnit> getCompilationUnits() {
        changeHistory.updateModel(); // update arrival of CU's
        return getKnownCompilationUnits();
    }

    public List<CompilationUnit> getKnownCompilationUnits() {
        int n = location2cu.size();
        List<CompilationUnit> res = new ArrayList<>(n);
        for (CompilationUnit cu : location2cu.values()) {
            res.add(cu);
        }
        return res;
    }

    public List<CompilationUnit> getAllCompilationUnitsFromPath() throws ParserException {
        return getAllCompilationUnitsFromPath(JAVA_FILENAME_FILTER);
    }

    public List<CompilationUnit> getAllCompilationUnitsFromPath(FilenameFilter filter)
            throws ParserException {
        DataLocation[] locations = getSearchPathList().findAll(filter);
        List<CompilationUnit> res = new ArrayList<>(locations.length);
        listeners.fireProgressEvent(0, res.size(), "Importing Source Files From Path");
        for (int i = 0; i < locations.length; i++) {
            listeners.fireProgressEvent(i, "Parsing " + locations[i]);
            CompilationUnit cu = getCompilationUnitFromLocation(locations[i]);
            res.add(cu);
        }
        listeners.fireProgressEvent(locations.length);
        return res;
    }

    public boolean isUpToDate(CompilationUnit cu) {
        Debug.assertNonnull(cu);
        if (cu.getDataLocation() == null) {
            return false;
        }
        return !changedUnits.contains(cu);
    }

    // create a new data location given the current position of the unit
    protected DataLocation createDataLocation(CompilationUnit cu) {
        String filename = Naming.toCanonicalFilename(cu);
        File f = new File(getOutputPath(), filename);
        return new DataFileLocation(f);
    }

    private void printUnit(CompilationUnit cu) throws IOException {
        DataLocation location = cu.getDataLocation();
        // create output path name
        if (location == null || cu.getOriginalDataLocation() == location) {
            if (location != null) {
                location2cu.remove(location);
            }
            location = createDataLocation(cu);
            cu.setDataLocation(location);
            location2cu.put(location, cu);
        }
        if (!location.isWritable()) {
            throw new IOException("Data location for " + location + " is not writable");
        }
        if (location instanceof DataFileLocation) {
            File f = ((DataFileLocation) location).getFile();
            File parent = new File(f.getParent());
            if (!parent.exists()) {
                parent.mkdirs();
            }
        }
        Writer w = location.getWriter();
        PrettyPrinter pprinter = serviceConfiguration.getProgramFactory().getPrettyPrinter(w);
        cu.accept(pprinter);
        w.flush();
        w.close();
        location.writerClosed();
    }

    public void print(CompilationUnit cu) throws IOException {
        Debug.assertNonnull(cu);
        printUnit(cu);
        changedUnits.remove(cu);
    }

    public void printAll(boolean always) throws IOException {
        changeHistory.updateModel(); // update arrival of new cu's
        int size = always ? location2cu.size() : changedUnits.size();
        listeners.fireProgressEvent(0, size, "Exporting Source Files");
        CompilationUnit[] units = new CompilationUnit[size];
        int j = 0;
        for (CompilationUnit cu : always ? location2cu.values() : changedUnits) {
            units[j++] = cu;
        }
        if (DEBUG) {
            Debug.log("printing...");
        }
        for (int i = 0; i < size; i += 1) {
            if (DEBUG) {
                Debug.log("units[i].getName()");
            }
            printUnit(units[i]);
            listeners.fireProgressEvent(i + 1, units[i]);
        }
        changedUnits.clear();
    }

    /**
     * Deletes all superfluous (renamed, detached) compilation unit files. Does not remove source
     * files from other sources.
     */
    public void cleanUp() {
        for (DataLocation loc : deleteUnits) {
            if (loc instanceof DataFileLocation) {
                File f = ((DataFileLocation) loc).getFile();
                f.delete();
            }
        }
        deleteUnits.clear();

    }

    public String information() {
        return "" + location2cu.size() + " compilation units (" + changedUnits.size()
            + " currently changed)";
    }

}
