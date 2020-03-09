// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util;

import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.zip.ZipFile;

import de.uka.ilkd.key.java.recoderext.URLDataLocation;
import org.key_project.util.Filenames;
import org.key_project.util.Strings;
import org.key_project.util.collection.*;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.RenamingTable;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import recoder.io.ArchiveDataLocation;
import recoder.io.DataFileLocation;
import recoder.io.DataLocation;

/**
 * Collection of some common, stateless functionality. Stolen from the weissInvariants side branch.
 */
public final class MiscTools {

    private MiscTools() {
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    // TODO Is rp always a program variable?
    public static ProgramVariable getSelf(MethodFrame mf) {
        ExecutionContext ec = (ExecutionContext) mf.getExecutionContext();
        ReferencePrefix rp = ec.getRuntimeInstance();
        if (!(rp instanceof TypeReference) && rp != null) {
            return (ProgramVariable) rp;
        } else {
            return null;
        }
    }

    /**
     * Returns the receiver term of the passed method frame, or null if the frame belongs to a
     * static method.
     *
     * @param mf a method frame.
     * @param services services.
     * @return the receiver term of the passed method frame, or null if the frame belongs to a
     * static method.
     */
    public static Term getSelfTerm(MethodFrame mf, Services services) {
        ExecutionContext ec = (ExecutionContext) mf.getExecutionContext();
        ReferencePrefix rp = ec.getRuntimeInstance();
        if (!(rp instanceof TypeReference) && rp != null) {
            return services.getTypeConverter().convertToLogicElement(rp);
        } else {
            return null;
        }
    }

    /**
     * All variables read in the specified program element, excluding newly declared variables.
     *
     * @param pe a program element.
     * @param services services.
     * @return all variables read in the specified program element,
     *  excluding newly declared variables.
     */
    public static ImmutableSet<ProgramVariable> getLocalIns(ProgramElement pe,
            Services services) {
        final ReadPVCollector rpvc = new ReadPVCollector(pe, services);
        rpvc.start();
        return rpvc.result();
    }

    /**
     * All variables changed in the specified program element, excluding newly declared variables.
     *
     * @param pe a program element.
     * @param services services.
     * @return all variables changed in the specified program element,
     *  excluding newly declared variables.
     */
    public static ImmutableSet<ProgramVariable> getLocalOuts(
            ProgramElement pe,
            Services services) {
        final WrittenAndDeclaredPVCollector wpvc = new WrittenAndDeclaredPVCollector(pe, services);
        wpvc.start();
        return wpvc.getWrittenPVs();
    }

    /**
     * All variables changed in the specified program element, including newly declared variables.
     *
     * @param pe a program element.
     * @param services services.
     * @return all variables changed in the specified program element,
     *  including newly declared variables.
     */
    public static ImmutableSet<ProgramVariable> getLocalOutsAndDeclared(
            ProgramElement pe,
            Services services) {
        final WrittenAndDeclaredPVCollector wpvc = new WrittenAndDeclaredPVCollector(pe, services);
        wpvc.start();
        return wpvc.getWrittenPVs().union(wpvc.getDeclaredPVs());
    }

    /**
     * All variables newly declared in the specified program element.
     *
     * @param pe a program element.
     * @param services services.
     * @return all variables newly declared in the specified program element.
     */
    public static ImmutableSet<ProgramVariable> getLocallyDeclaredVars(
            ProgramElement pe,
            Services services) {
        final WrittenAndDeclaredPVCollector wpvc = new WrittenAndDeclaredPVCollector(pe, services);
        wpvc.start();
        return wpvc.getDeclaredPVs();
    }

    /**
     * Recursively collect all observers for this term including all of its sub terms.
     * @param t the term for which we want to collect the observer functions.
     * @return the observers as a set of pairs with sorts and according observers
     */
    public static ImmutableSet<Pair<Sort, IObserverFunction>> collectObservers(Term t) {
        ImmutableSet<Pair<Sort, IObserverFunction>> result = DefaultImmutableSet.nil();
        if (t.op() instanceof IObserverFunction) {
            final IObserverFunction obs = (IObserverFunction) t.op();
            final Sort s = obs.isStatic()
                    ? obs.getContainerType().getSort()
                    : t.sub(1).sort();
            result = result.add(new Pair<Sort, IObserverFunction>(s, obs));
        }
        for (Term sub : t.subs()) {
            result = result.union(collectObservers(sub));
        }
        return result;
    }


    /**
     * True if both are <code>null</code> or <code>a.equals(b)</code> with <code>equals</code> from type T.
     * You should use {@link Objects#equals(Object, Object)} directly.
     */
    @Deprecated
    public static <T> boolean equalsOrNull(T a, Object b) {
        return Objects.equals(a, b);
        /*if (a == null) {
            return b == null;
        } else {
            return a.equals(b);
        }*/
    }

    /**
     * {@code true} iff all are <code>null</code> or <code>a.equals(b)</code>
     * with <code>equals</code> from type T for every {@code b}.
     *
     * @param a an object.
     * @param bs other object.
     * @param <T> type of {@code a} and result value.
     * @return {@code true} iff all are <code>null</code> or <code>a.equals(b)</code>
     *  with <code>equals</code> from type T for every {@code b}.
     */
    public static <T> boolean equalsOrNull(T a, Object... bs) {
        boolean result = true;
        for (Object b : bs) {
            result = result && equalsOrNull(a, b);
        }
        return result;
    }

    // =======================================================
    // Methods operating on Arrays
    // =======================================================

    /**
     * Concatenates two arrays.
     *
     * @param s1 an array.
     * @param s2 another array.
     * @param <S> type o array {@code s1} and of result array.
     * @param <T> type of array {@code s2}.
     * @return the concatenation of both arrays.
     */
    public static <S, T extends S> S[] concat(S[] s1, T[] s2) {
        return KeYCollections.concat(s1,s2);
    }

    // =======================================================
    // Methods operating on Collections
    // =======================================================

    /**
     * Combine two maps by function application. Values of <code>m0</code> which are not keys of
     * <code>m1</code> are dropped. This implementation tries to use the same implementation of
     * {@link java.util.Map} (provided in Java SE) as <code>m0</code>.
     *
     * @param m0 a map.
     * @param m1 another map.
     * @param <S> type of {@code m0}.
     * @param <T> type of {@code m1}.
     * @param <U> new type of result map indexes.
     * @return the combination of both maps.
     */
    public static <S, T, U> Map<S, U> apply(Map<S, ? extends T> m0, Map<T, U> m1) {
        return KeYCollections.apply(m0, m1);
    }

    // =======================================================
    // Methods operating on Strings
    // =======================================================

    /**
     * Separates the single directory entries in a filename. The first element is an empty String
     * iff the filename is absolute. (For a Windows filename, it contains a drive letter and a
     * colon). Ignores double slashes and slashes at the end, removes references to the cwd. E.g.,
     * "/home//daniel/./key/" yields {"","home","daniel","key"}. Tries to automatically detect UNIX
     * or Windows directory delimiters. There is no check whether all other characters are valid for
     * filenames.
     *
     * @param filename a file name.
     * @return all directory entries in the file name.
     */
    static List<String> disectFilename(String filename) {
        return Filenames.disectFilename(filename);
    }

    /**
     * Returns a filename relative to another one. The second parameter needs to be absolute and is
     * expected to refer to a directory. This method only operates on Strings, not on real files!
     * Note that it treats Strings case-sensitive. The resulting filename always uses UNIX
     * directory delimiters. Raises a RuntimeException if no relative path could be found (may
     * happen on Windows systems).
     *
     * @param origFilename a filename.
     * @param toFilename the name of a parent directory of {@code origFilename}.
     * @return {@code origFilename} relative to {@code toFilename}
     */
    public static String makeFilenameRelative(String origFilename, String toFilename) {
        return Filenames.makeFilenameRelative(origFilename, toFilename);
    }

    public static Name toValidTacletName(String s) {
        s = s.replaceAll("\\s|\\.|::\\$|::|<|>|/", "_");
        return new Name(s);
    }

    public static String toValidFileName(String s) {
        s = s.replace("\\", "_")
                .replace("$", "_")
                .replace("?", "_")
                .replace("|", "_")
                .replace("<", "_")
                .replace(">", "_")
                .replace(":", "_")
                .replace("*", "+")
                .replace("\"", "'")
                .replace("/", "-")
                .replace("[", "(")
                .replace("]", ")");
        return s;
    }

    public static Name toValidVariableName(String s) {
        s = s.replaceAll("\\s|\\.|::\\$|::|<|>|/|\\(|\\)|,", "_");
        return new Name(s);
    }

    /**
     * Join the string representations of a collection of objects into onw string. The individual
     * elements are separated by a delimiter.
     *
     * {@link Object#toString()} is used to turn the objects into strings.
     *
     * @param collection an arbitrary non-null collection
     * @param delimiter  a non-null string which is put between the elements.
     *
     * @return the concatenation of all string representations separated by the delimiter
     */
    public static String join(Iterable<?> collection, String delimiter) {
        return KeYCollections.join(collection, delimiter);
    }

    /**
     * Join the string representations of an array of objects into one string. The individual
     * elements are separated by a delimiter.
     *
     * {@link Object#toString()} is used to turn the objects into strings.
     *
     * @param collection an arbitrary non-null array of objects
     * @param delimiter  a non-null string which is put between the elements.
     *
     * @return the concatenation of all string representations separated by the delimiter
     */
    public static String join(Object[] collection, String delimiter) {
        return KeYCollections.join(collection, delimiter);
    }

    /**
     * Takes a string and returns a string which is potentially shorter and contains a
     * sub-collection of the original characters.
     *
     * All alphabetic characters (A-Z and a-z) are copied to the result while all other characters
     * are removed.
     *
     * @param string an arbitrary string
     * @return a string which is a sub-structure of the original character sequence
     *
     * @author Mattias Ulbrich
     */
    public static /* @ non_null @ */ String filterAlphabetic(/* @ non_null @ */ String string) {
        return KeYCollections.filterAlphabetic(string);
    }

    /**
     * Checks whether a string contains another one as a whole word (i.e., separated by
     * white spaces or a semicolon at the end).
     *
     * @param s    string to search in
     * @param word string to be searched for
     * @return the answer to the question specified above
     */
    public static boolean containsWholeWord(String s, String word) {
        return Strings.containsWholeWord(s, word);
    }

    /**
     * There are different kinds of JML markers. See Section 4.4 "Annotation markers" of the JML
     * reference manual.
     *
     * @param comment
     * @return
     */
    public static boolean isJMLComment(String comment) {
        return Strings.isJMLComment(comment);
    }

    /**
     * <p>
     * Returns the display name of the applied rule in the given {@link Node} of the proof tree in
     * KeY.
     * </p>
     * <p>
     * This method is required for the symbolic execution tree extraction, e.g. used in the Symbolic
     * Execution Tree Debugger.
     * </p>
     *
     * @param node The given {@link Node}.
     * @return The display name of the applied rule in the given {@link Node} or {@code null} if no
     *         one exists.
     */
    public static String getRuleDisplayName(Node node) {
        String name = null;
        if (node != null) {
            name = getRuleDisplayName(node.getAppliedRuleApp());
        }
        return name;
    }

    /**
     * <p>
     * Returns the display name of the {@link RuleApp}.
     * </p>
     * <p>
     * This method is required for the symbolic execution tree extraction, e.g. used in the Symbolic
     * Execution Tree Debugger.
     * </p>
     *
     * @param ruleApp The given {@link RuleApp}.
     * @return The display name of the {@link RuleApp} or {@code null} if no one exists.
     */
    public static String getRuleDisplayName(RuleApp ruleApp) {
        String name = null;
        if (ruleApp != null) {
            Rule rule = ruleApp.rule();
            if (rule != null) {
                name = rule.displayName();
            }
        }
        return name;
    }

    /**
     * <p>
     * Returns the name of the applied rule in the given {@link Node} of the proof tree in KeY.
     * </p>
     * <p>
     * This method is required for the symbolic execution tree extraction, e.g. used in the Symbolic
     * Execution Tree Debugger.
     * </p>
     *
     * @param node The given {@link Node}.
     * @return The display name of the applied rule in the given {@link Node} or {@code null} if no
     *         one exists.
     */
    public static String getRuleName(Node node) {
        String name = null;
        if (node != null) {
            name = getRuleName(node.getAppliedRuleApp());
        }
        return name;
    }

    /**
     * <p>
     * Returns the name of the {@link RuleApp}.
     * </p>
     * <p>
     * This method is required for the symbolic execution tree extraction, e.g. used in the Symbolic
     * Execution Tree Debugger.
     * </p>
     *
     * @param ruleApp The given {@link RuleApp}.
     * @return The display name of the {@link RuleApp} or {@code null} if no one exists.
     */
    public static String getRuleName(RuleApp ruleApp) {
        String name = null;
        if (ruleApp != null) {
            Rule rule = ruleApp.rule();
            if (rule != null) {
                name = rule.name().toString();
            }
        }
        return name;
    }

    /**
     * Returns the {@link OneStepSimplifier} used in the given {@link Proof}.
     *
     * @param proof The {@link Proof} to get its used {@link OneStepSimplifier}.
     * @return The used {@link OneStepSimplifier} or {@code null} if not available.
     */
    public static OneStepSimplifier findOneStepSimplifier(Proof proof) {
        if (proof != null && !proof.isDisposed() && proof.getInitConfig() != null) {
            Profile profile = proof.getInitConfig().getProfile();
            return findOneStepSimplifier(profile);
        } else {
            return null;
        }
    }

    /**
     * Returns the {@link OneStepSimplifier} used in the given {@link Profile}.
     *
     * @param profile The {@link Profile} to get its used {@link OneStepSimplifier}.
     * @return The used {@link OneStepSimplifier} or {@code null} if not available.
     */
    public static OneStepSimplifier findOneStepSimplifier(Profile profile) {
        if (profile instanceof JavaProfile) {
            return ((JavaProfile) profile).getOneStepSimpilifier();
        } else {
            return null;
        }
    }

    /**
     * Returns the actual variable for a given one (this means it returns the renamed variable).
     *
     * @param node the Node where to look up the actual variable (result from renaming)
     * @return The renamed variable
     */
    public static ProgramVariable findActualVariable(ProgramVariable originalVar, Node node) {
        ProgramVariable actualVar = originalVar;
        if (node != null) {
            outer: do {
                if (node.getRenamingTable() != null) {
                    for (RenamingTable rt : node.getRenamingTable()) {
                        ProgramVariable renamedVar = (ProgramVariable) rt.getRenaming(actualVar);
                        if (renamedVar != null || !node.getLocalProgVars().contains(actualVar)) {
                            actualVar = renamedVar;
                            break outer;
                        }
                    }
                }
                node = node.parent();
            } while (node != null);
        }
        return actualVar;
    }

    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    private static final class ReadPVCollector extends JavaASTVisitor {
        /**
         * The list of resulting (i.e., read) program variables.
         */
        private ImmutableSet<ProgramVariable> result = DefaultImmutableSet.<ProgramVariable>nil();

        /**
         * The declared program variables.
         */
        private ImmutableSet<ProgramVariable> declaredPVs = DefaultImmutableSet
                .<ProgramVariable>nil();

        public ReadPVCollector(ProgramElement root, Services services) {
            super(root, services);
        }

        @Override
        protected void doDefaultAction(SourceElement node) {
            if (node instanceof ProgramVariable) {
                ProgramVariable pv = (ProgramVariable) node;
                if (!pv.isMember() && !declaredPVs.contains(pv)) {
                    result = result.add(pv);
                }
            } else if (node instanceof VariableSpecification) {
                VariableSpecification vs = (VariableSpecification) node;
                ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
                if (!pv.isMember()) {
                    assert !declaredPVs.contains(pv);
                    result = result.remove(pv);
                    declaredPVs = declaredPVs.add(pv);
                }
            }
        }

        public ImmutableSet<ProgramVariable> result() {
            return result;
        }
    }

    private static class WrittenAndDeclaredPVCollector extends JavaASTVisitor {
        /**
         * The written program variables.
         */
        private ImmutableSet<ProgramVariable> writtenPVs =
                DefaultImmutableSet.<ProgramVariable>nil();

        /**
         * The declared program variables.
         */
        private ImmutableSet<ProgramVariable> declaredPVs =
                DefaultImmutableSet.<ProgramVariable>nil();

        public WrittenAndDeclaredPVCollector(ProgramElement root, Services services) {
            super(root, services);
        }

        @Override
        protected void doDefaultAction(SourceElement node) {
            if (node instanceof Assignment) {
                ProgramElement lhs = ((Assignment) node).getChildAt(0);
                if (lhs instanceof ProgramVariable) {
                    ProgramVariable pv = (ProgramVariable) lhs;
                    if (!pv.isMember() && !declaredPVs.contains(pv)) {
                        writtenPVs = writtenPVs.add(pv);
                    }
                }
            } else if (node instanceof VariableSpecification) {
                VariableSpecification vs = (VariableSpecification) node;
                ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
                if (!pv.isMember()) {
                    assert !declaredPVs.contains(pv);
                    assert !writtenPVs.contains(pv);
                    declaredPVs = declaredPVs.add(pv);
                }
            }
        }

        public ImmutableSet<ProgramVariable> getWrittenPVs() {
            return writtenPVs;
        }

        public ImmutableSet<ProgramVariable> getDeclaredPVs() {
            return declaredPVs;
        }
    }

    public static ImmutableList<Term> toTermList(Iterable<ProgramVariable> list,
            TermBuilder tb) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (ProgramVariable pv : list) {
            if (pv != null) {
                Term t = tb.var(pv);
                result = result.append(t);
            }
        }
        return result;
    }

    /**
     * read an input stream to its end into a string.
     *
     * @param is a non-null open input stream
     * @return the string created from the input of the stream
     * @throws IOException may occur while reading the stream
     */
    public static String toString(InputStream is) throws IOException {
        StringBuilder sb = new StringBuilder();
        byte[] buffer = new byte[2048];
        int read;
        while ((read = is.read(buffer)) > 0) {
            sb.append(new String(buffer, 0, read));
        }
        return sb.toString();
    }

    public static ImmutableList<Term> filterOutDuplicates(ImmutableList<Term> localIns,
            ImmutableList<Term> localOuts) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (Term localIn : localIns) {
            if (!localOuts.contains(localIn)) {
                result = result.append(localIn);
            }
        }
        return result;
    }

    /**
     * Returns the default taclet options.
     *
     * @return The default taclet options.
     */
    public static HashMap<String, String> getDefaultTacletOptions() {
        HashMap<String, String> result = new HashMap<String, String>();
        result.put("Strings", "Strings:on");
        result.put("reach", "reach:on");
        result.put("JavaCard", "JavaCard:off");
        result.put("assertions", "assertions:on");
        result.put("bigint", "bigint:on");
        result.put("intRules", "intRules:arithmeticSemanticsIgnoringOF");
        result.put("programRules", "programRules:Java");
        result.put("modelFields", "modelFields:showSatisfiability");
        result.put("initialisation", "initialisation:disableStaticInitialisation");
        result.put("sequences", "sequences:on");
        result.put("runtimeExceptions", "runtimeExceptions:allow");
        result.put("integerSimplificationRules", "integerSimplificationRules:full");
        result.put("optimisedSelectRules", "optimisedSelectRules:on");
        result.put("wdChecks", "wdChecks:off");
        result.put("wdOperator", "wdOperator:L");
        result.put("permissions", "permissions:off");
        return result;
    }

    /**
     * Returns the path to the source file defined by the given {@link PositionInfo}.
     *
     * @param posInfo The {@link PositionInfo} to extract source file from.
     * @return The source file name or {@code null} if not available.
     */
    public static String getSourcePath(PositionInfo posInfo) {
        String result = null;
        if (posInfo.getFileName() != null) {
            result = posInfo.getFileName(); // posInfo.getFileName() is a path to a file
        } else if (posInfo.getParentClass() != null) {
            result = posInfo.getParentClass(); // posInfo.getParentClass() is a path to a file
        }
        if (result != null && result.startsWith("FILE:")) {
            result = result.substring("FILE:".length());
        }
        return result;
    }

    /**
     * Tries to extract a valid URI from the given DataLocation.
     * @param loc the given DataLocation
     * @return an URI identifying the resource of the DataLocation
     */
    public static URI extractURI(DataLocation loc) {
        if (loc == null) {
            throw new IllegalArgumentException("The given DataLocation is null!");
        }

        try {
            switch (loc.getType()) {
            case "URL":                                                     // URLDataLocation
                return ((URLDataLocation)loc).getUrl().toURI();
            case "ARCHIVE":                                                 // ArchiveDataLocation
                // format: "ARCHIVE:<filename>?<itemname>"
                ArchiveDataLocation adl = (ArchiveDataLocation) loc;

                // extract item name and zip file
                int qmindex = adl.toString().lastIndexOf('?');
                String itemName = adl.toString().substring(qmindex + 1);
                ZipFile zip = adl.getFile();

                // use special method to ensure that path separators are correct
                return getZipEntryURI(zip, itemName);
            case "FILE":                                                    // DataFileLocation
                // format: "FILE:<path>"
                return ((DataFileLocation)loc).getFile().toURI();
            default:                                                        // SpecDataLocation
                // format "<type>://<location>"
                // wrap into URN to ensure URI encoding is correct (no spaces!)
                return new URI("urn", loc.toString(), null);
            }
        } catch (URISyntaxException | IOException e) {
            e.printStackTrace();
        }
        throw new IllegalArgumentException("The given DataLocation can not be converted" +
                " into a valid URI: " + loc);
    }

    /**
     * Creates a URI (that contains a URL) pointing to the entry with the given name inside
     * the given zip file.
     * <br><br>
     * <b>Note:</b> There is an unresolved bug in Java for JarURLs when the jar path
     * contains a directory ending with "!"
     * ("!" should be encoded as "%21", but is not).
     * In this case, the program will crash if trying to open a resource from the url.
     * This will not be fixed until {@link java.net.URI} supports RFC 3986
     * (currently, as of 02-2020, it seems like there are no plans for this).<br>
     * <b>Workaround:</b> Don't use directory names ending with "!".
     * @param zipFile the given zip
     * @param entryName the entry path relative to the root of the zip
     * @return a zip/jar URI to the entry inside the zip
     * @throws IOException if an I/O error occurs
     */
    public static URI getZipEntryURI(ZipFile zipFile, String entryName) throws IOException {

        Path zipPath = Paths.get(zipFile.getName());

        // TODO: Delete these lines when migrating to newer Java version!
        // These lines are needed since there is a bug in Java (up to Java 9 b80)
        // where special characters such as spaces in URI get double encoded.
        // see https://bugs.java.com/bugdatabase/view_bug.do?bug_id=8131067
        // To make it even worse, this happens only in the part before "!/".
        // We manually build our URI to ensure the encoding is correct:
        try {
            URI zipURI = zipPath.toUri();
            URI entry = new URI(null, null, entryName, null);

            // we have to cut off the starting slash if there is one
            String entryStr = entry.toString();
            entryStr = entryStr.startsWith("/") ? entryStr.substring(1) : entryStr;

            return new URI("jar:" + zipURI + "!/" + entryStr);
        } catch (URISyntaxException e) {
            throw new IOException(e);
        }

        // TODO: This should be enough if we use a Java  version newer than 9 b80!
        //try (FileSystem fs = FileSystems.newFileSystem(zipPath, null)) {
        //    Path p = fs.getPath(entryName);
        //    return p.toUri();
        //}
    }
}
