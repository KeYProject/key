/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.ZipFile;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.recoderext.URLDataLocation;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.LoopSpecification;

import org.key_project.util.Filenames;
import org.key_project.util.Strings;
import org.key_project.util.collection.*;

import org.antlr.v4.runtime.IntStream;
import org.antlr.v4.runtime.TokenSource;
import recoder.io.ArchiveDataLocation;
import recoder.io.DataFileLocation;
import recoder.io.DataLocation;

/**
 * Collection of some common, stateless functionality. Stolen from the weissInvariants side branch.
 */
public final class MiscTools {

    /** Pattern to parse URL scheme (capture group 1) and scheme specific part (group 2). */
    private static final Pattern URL_PATTERN =
        Pattern.compile("(^[a-zA-Z][a-zA-Z0-9\\+\\-\\.]*):(.*)");

    private MiscTools() {
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Returns the {@link LoopSpecification} for the program in the given term, the active statement
     * of which has to be a loop statement. Returns an empty {@link Optional} if there is no
     * specification for that statement. Asserts that there is indeed a Java block in the term which
     * has as active statement a loop statement, thus throws an {@link AssertionError} if not or
     * otherwise results in undefined behavior in that case.
     *
     * @param loopTerm The term for which to return the {@link LoopSpecification}.
     * @return The {@link LoopSpecification} for the loop statement in the given term or an empty
     *         optional if there is no specified invariant for the loop.
     */
    public static Optional<LoopSpecification> getSpecForTermWithLoopStmt(final Term loopTerm,
            final Services services) {
        assert loopTerm.op() instanceof Modality;
        assert loopTerm.javaBlock() != JavaBlock.EMPTY_JAVABLOCK;

        final ProgramElement pe = loopTerm.javaBlock().program();
        assert pe != null;
        assert pe instanceof StatementBlock;
        assert pe.getFirstElement() instanceof LoopStatement;

        final LoopStatement loop = //
            (LoopStatement) pe.getFirstElement();

        return Optional.ofNullable(services.getSpecificationRepository().getLoopSpec(loop));
    }

    /**
     * @param services The {@link Services} object.
     * @return true iff the given {@link Services} object is associated to a {@link Profile} with
     *         permissions.
     */
    public static boolean isPermissions(Services services) {
        return services.getProfile() instanceof JavaProfile
                && ((JavaProfile) services.getProfile()).withPermissions();
    }

    /**
     * Checks whether the given {@link Modality} is a transaction modality.
     *
     * @param modality The modality to check.
     * @return true iff the given {@link Modality} is a transaction modality.
     */
    public static boolean isTransaction(final Modality modality) {
        return modality == Modality.BOX_TRANSACTION || modality == Modality.DIA_TRANSACTION;
    }

    /**
     * Returns the applicable heap contexts out of the currently available set of three contexts:
     * The normal heap, the saved heap (transaction), and the permission heap.
     *
     * @param modality The current modality (checked for transaction).
     * @param services The {@link Services} object (for {@link HeapLDT} and for checking whether
     *        we're in the permissions profile).
     * @return The list of the applicable heaps for the given scenario.
     */
    public static List<LocationVariable> applicableHeapContexts(Modality modality,
            Services services) {
        final List<LocationVariable> result = new ArrayList<>();

        result.add(services.getTypeConverter().getHeapLDT().getHeap());

        if (isTransaction(modality)) {
            result.add(services.getTypeConverter().getHeapLDT().getSavedHeap());
        }

        if (isPermissions(services)) {
            result.add(services.getTypeConverter().getHeapLDT().getPermissionHeap());
        }
        return result;
    }

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
     *         static method.
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
     * @return all variables read in the specified program element, excluding newly declared
     *         variables.
     */
    public static ImmutableSet<ProgramVariable> getLocalIns(ProgramElement pe, Services services) {
        final ReadPVCollector rpvc = new ReadPVCollector(pe, services);
        rpvc.start();
        return rpvc.result();
    }

    /**
     * All variables changed in the specified program element, excluding newly declared variables.
     *
     * @param pe a program element.
     * @param services services.
     * @return all variables changed in the specified program element, excluding newly declared
     *         variables.
     */
    public static ImmutableSet<ProgramVariable> getLocalOuts(ProgramElement pe, Services services) {
        final WrittenAndDeclaredPVCollector wpvc = new WrittenAndDeclaredPVCollector(pe, services);
        wpvc.start();
        return wpvc.getWrittenPVs();
    }

    /**
     * All variables changed in the specified program element, including newly declared variables.
     *
     * @param pe a program element.
     * @param services services.
     * @return all variables changed in the specified program element, including newly declared
     *         variables.
     */
    public static ImmutableSet<ProgramVariable> getLocalOutsAndDeclared(ProgramElement pe,
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
    public static ImmutableSet<ProgramVariable> getLocallyDeclaredVars(ProgramElement pe,
            Services services) {
        final WrittenAndDeclaredPVCollector wpvc = new WrittenAndDeclaredPVCollector(pe, services);
        wpvc.start();
        return wpvc.getDeclaredPVs();
    }

    /**
     * Recursively collect all observers for this term including all of its sub terms.
     *
     * @param t the term for which we want to collect the observer functions.
     * @return the observers as a set of pairs with sorts and according observers
     */
    public static ImmutableSet<Pair<Sort, IObserverFunction>> collectObservers(Term t) {
        ImmutableSet<Pair<Sort, IObserverFunction>> result = DefaultImmutableSet.nil();
        if (t.op() instanceof IObserverFunction) {
            final IObserverFunction obs = (IObserverFunction) t.op();
            final Sort s = obs.isStatic() ? obs.getContainerType().getSort() : t.sub(1).sort();
            result = result.add(new Pair<>(s, obs));
        }
        for (Term sub : t.subs()) {
            result = result.union(collectObservers(sub));
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
        return KeYCollections.concat(s1, s2);
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
     * Note that it treats Strings case-sensitive. The resulting filename always uses UNIX directory
     * delimiters. Raises a RuntimeException if no relative path could be found (may happen on
     * Windows systems).
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

    /**
     * Remove the file extension (.key, .proof) from the given filename.
     *
     * @param filename file name
     * @return file name without .key or .proof extension
     */
    public static String removeFileExtension(String filename) {
        if (filename.endsWith(".key")) {
            return filename.substring(0, filename.length() - ".key".length());
        } else if (filename.endsWith(".proof")) {
            return filename.substring(0, filename.length() - ".proof".length());
        } else {
            return filename;
        }
    }

    public static String toValidFileName(String s) {
        return s.replace("\\", "_")
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
     * @param delimiter a non-null string which is put between the elements.
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
     * @param delimiter a non-null string which is put between the elements.
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
     * Checks whether a string contains another one as a whole word (i.e., separated by white spaces
     * or a semicolon at the end).
     *
     * @param s string to search in
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
        if (node != null) {
            do {
                if (node.getRenamingTable() != null) {
                    for (RenamingTable rt : node.getRenamingTable()) {
                        ProgramVariable renamedVar = (ProgramVariable) rt.getRenaming(originalVar);
                        if (renamedVar != null || !node.getLocalProgVars().contains(originalVar)) {
                            return renamedVar;
                        }
                    }
                }
                node = node.parent();
            } while (node != null);
        }
        return originalVar;
    }

    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    private static final class ReadPVCollector extends JavaASTVisitor {
        /**
         * The list of resulting (i.e., read) program variables.
         */
        private ImmutableSet<ProgramVariable> result = DefaultImmutableSet.nil();

        /**
         * The declared program variables.
         */
        private ImmutableSet<ProgramVariable> declaredPVs =
            DefaultImmutableSet.nil();

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
            DefaultImmutableSet.nil();

        /**
         * The declared program variables.
         */
        private ImmutableSet<ProgramVariable> declaredPVs =
            DefaultImmutableSet.nil();

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

    public static ImmutableList<Term> toTermList(Iterable<ProgramVariable> list, TermBuilder tb) {
        ImmutableList<Term> result = ImmutableSLList.nil();
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
            sb.append(new String(buffer, 0, read, StandardCharsets.UTF_8));
        }
        return sb.toString();
    }

    public static ImmutableList<Term> filterOutDuplicates(ImmutableList<Term> localIns,
            ImmutableList<Term> localOuts) {
        ImmutableList<Term> result = ImmutableSLList.nil();
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
        HashMap<String, String> result = new HashMap<>();
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
     * Tries to extract a valid URI from the given DataLocation.
     *
     * @param loc the given DataLocation
     * @return an URI identifying the resource of the DataLocation
     */
    public static Optional<URI> extractURI(DataLocation loc) {
        if (loc == null) {
            throw new IllegalArgumentException("The given DataLocation is null!");
        }

        try {
            switch (loc.getType()) {
            case "URL": // URLDataLocation
                return Optional.of(((URLDataLocation) loc).getUrl().toURI());
            case "ARCHIVE": // ArchiveDataLocation
                // format: "ARCHIVE:<filename>?<itemname>"
                ArchiveDataLocation adl = (ArchiveDataLocation) loc;

                // extract item name and zip file
                int qmindex = adl.toString().lastIndexOf('?');
                String itemName = adl.toString().substring(qmindex + 1);
                ZipFile zip = adl.getFile();

                // use special method to ensure that path separators are correct
                return Optional.of(getZipEntryURI(zip, itemName));
            case "FILE": // DataFileLocation
                // format: "FILE:<path>"
                return Optional.of(((DataFileLocation) loc).getFile().toURI());
            default: // SpecDataLocation
                // format "<type>://<location>"
                // wrap into URN to ensure URI encoding is correct (no spaces!)
                return Optional.empty();
            }
        } catch (URISyntaxException | IOException e) {
            throw new IllegalArgumentException(
                "The given DataLocation can not be converted into a valid URI: " + loc, e);
        }
    }

    /**
     * Creates a URI (that contains a URL) pointing to the entry with the given name inside the
     * given zip file. <br>
     * <br>
     * <b>Note:</b> There is an unresolved bug in Java for JarURLs when the jar path contains a
     * directory ending with "!" ("!" should be encoded as "%21", but is not). In this case, the
     * program will crash if trying to open a resource from the url. This will not be fixed until
     * {@link java.net.URI} supports RFC 3986 (currently, as of 02-2020, it seems like there are no
     * plans for this).<br>
     * <b>Workaround:</b> Don't use directory names ending with "!".
     *
     * @param zipFile the given zip
     * @param entryName the entry path relative to the root of the zip
     * @return a zip/jar URI to the entry inside the zip
     * @throws IOException if an I/O error occurs
     */
    public static URI getZipEntryURI(ZipFile zipFile, String entryName) throws IOException {

        Path zipPath = Paths.get(zipFile.getName()).toAbsolutePath().normalize();

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

        // TODO: This should be enough if we use a Java version newer than 9 b80!
        // try (FileSystem fs = FileSystems.newFileSystem(zipPath, null)) {
        // Path p = fs.getPath(entryName);
        // return p.toUri();
        // }
    }

    @Nullable
    public static URI getURIFromTokenSource(TokenSource source) {
        return getURIFromTokenSource(source.getSourceName());
    }

    @Nullable
    public static URI getURIFromTokenSource(String source) {
        if (IntStream.UNKNOWN_SOURCE_NAME.equals(source)) {
            return null;
        }

        try {
            return new URI(source);
        } catch (URISyntaxException ignored) {
        }
        return Path.of(source).toUri();
    }

    /**
     * This method is the central place for parsing a URL from a String. Allowed input formats are:
     * <ul>
     * <li>from DataLocation:
     * <ul>
     * <li>URLDataLocation: URL:&lt;url&gt;</li>
     * <li>ArchiveDataLocation: ARCHIVE:&lt;filename&gt;?&lt;entry&gt;</li>
     * <li>FileDataLocation: FILE:&lt;filename&gt;</li>
     * <li>SpecDataLocation: &lt;type&gt;://&lt;location&gt;</li>
     * </ul>
     * </li>
     * <li>from URL: &lt;scheme&gt;:&lt;scheme_specific_part&gt;</li>
     * <li>from File/Path (in both cases, paths may be relative and/or not normalized!):
     * <ul>
     * <li>Unix: /a/b/c</li>
     * <li>Windows: &lt;drive_letter&gt;:\a\b\c\</li>
     * </ul>
     * </li>
     * </ul>
     *
     * A NullPointerException is thrown if null is given. If the input is "", ".", or a relative
     * path in general, the path is resolved against the current working directory (see system
     * property "user.dir") consistently to the behaviour of {@link Paths#get(String, String...)}.
     *
     * @param input the String to convert
     * @return a URL if successful
     * @throws MalformedURLException if the string can not be converted to URL because of an unknown
     *         protocol or illegal format
     */
    public static URL parseURL(final String input) throws MalformedURLException {
        if (input == null) {
            throw new NullPointerException("No URL can be created from null!");
        }

        String scheme = "";
        String schemeSpecPart = "";
        Matcher m = URL_PATTERN.matcher(input);
        if (m.matches() && m.groupCount() == 2) {
            scheme = m.group(1);
            schemeSpecPart = m.group(2);
        }
        switch (scheme) {
        case "URL":
            // schemeSpecPart actually contains a URL again
            return new URL(schemeSpecPart);
        case "ARCHIVE":
            // format: "ARCHIVE:<filename>?<itemname>"
            // extract item name and zip file
            int qmindex = schemeSpecPart.lastIndexOf('?');
            String zipName = schemeSpecPart.substring(0, qmindex);
            String itemName = schemeSpecPart.substring(qmindex + 1);

            try {
                ZipFile zip = new ZipFile(zipName);
                // use special method to ensure that path separators are correct
                return getZipEntryURI(zip, itemName).toURL();
            } catch (IOException e) {
                MalformedURLException me =
                    new MalformedURLException(input + " does not contain a valid URL");
                me.initCause(e);
                throw me;
            }
        case "FILE":
            // format: "FILE:<path>"
            Path path = Paths.get(schemeSpecPart).toAbsolutePath().normalize();
            return path.toUri().toURL();
        case "":
            // only file/path without protocol
            Path p = Paths.get(input).toAbsolutePath().normalize();
            return p.toUri().toURL();
        default:
            // may still be Windows path starting with <drive_letter>:
            if (scheme.length() == 1) {
                // TODO: Theoretically, a protocol with only a single letter is allowed.
                // This (very rare) case currently is not handled correctly.
                Path windowsPath = Paths.get(input).toAbsolutePath().normalize();
                return windowsPath.toUri().toURL();
            }
            // otherwise call URL constructor
            // if this also fails, there is an unknown protocol -> MalformedURLException
            return new URL(input);
        }
    }
}
