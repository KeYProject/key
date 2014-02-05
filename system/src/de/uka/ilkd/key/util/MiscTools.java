// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.util;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
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
import de.uka.ilkd.key.logic.Term;
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


/**
 * Collection of some common, stateless functionality. Stolen from
 * the weissInvariants side branch.
 */
public final class MiscTools {


    private MiscTools() {}


    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------


    // TODO Is rp always a program variable?
    public static ProgramVariable getSelf(MethodFrame mf) {
        ExecutionContext ec = (ExecutionContext) mf.getExecutionContext();
        ReferencePrefix rp = ec.getRuntimeInstance();
        if(!(rp instanceof TypeReference) && rp != null) {
            return (ProgramVariable) rp;
        } else {
            return null;
        }
    }


    /**
     * Returns the receiver term of the passed method frame, or null if
     * the frame belongs to a static method.
     */
    public static Term getSelfTerm(MethodFrame mf, Services services) {
	ExecutionContext ec = (ExecutionContext) mf.getExecutionContext();
	ReferencePrefix rp = ec.getRuntimeInstance();
	if(!(rp instanceof TypeReference) && rp != null) {
	    return services.getTypeConverter().convertToLogicElement(rp);
	} else {
	    return null;
	}
    }

    public static ImmutableSet<ProgramVariable> getLocalIns(ProgramElement pe,
	    					     	    Services services) {
	final ReadPVCollector rpvc = new ReadPVCollector(pe, services);
	rpvc.start();
	return rpvc.result();
    }


    public static ImmutableSet<ProgramVariable> getLocalOuts(
	    					ProgramElement pe,
	    			                Services services) {
	final WrittenPVCollector wpvc = new WrittenPVCollector(pe, services);
	wpvc.start();
	return wpvc.result();
    }


    public static ImmutableSet<Pair<Sort,IObserverFunction>>
    						collectObservers(Term t) {
	ImmutableSet<Pair<Sort, IObserverFunction>> result
		= DefaultImmutableSet.nil();
	if(t.op() instanceof IObserverFunction) {
	    final IObserverFunction obs = (IObserverFunction)t.op();
	    final Sort s = obs.isStatic()
	             	   ? obs.getContainerType().getSort()
	                   : t.sub(1).sort();
	    result = result.add(new Pair<Sort,IObserverFunction>(s, obs));
	}
	for(Term sub : t.subs()) {
	    result = result.union(collectObservers(sub));
	}
	return result;
    }

    /**
     * True if both are <code>null</code> or <code>a.equals(b)</code> with <code>equals</code> from type T.
     */
    public static <T> boolean equalsOrNull(T a, Object b){
        if (a == null) {
            return b == null;
        } else {
            return a.equals(b);
        }
    }

    public static <T> boolean equalsOrNull(T a, Object... bs){
        boolean result = true;
        for (Object b: bs){
            result = result && equalsOrNull(a, b);
        }
        return result;
    }


    // =======================================================
    // Methods operating on Collections
    // =======================================================

    /** Combine two maps by function application.
     * Values of <code>m0</code> which are not keys of <code>m1</code>
     * are dropped.
     * This implementation tries to use the same implementation of {@link java.util.Map}
     * (provided in Java SE) as <code>m0</code>.
     */
    public static <S,T,U> Map<S,U> apply(Map<S,? extends T> m0, Map<T,U> m1) {
        Map<S,U> res = null;
        final int size = m0.size() < m1.size()? m0.size(): m1.size();
        // try to use more specific implementation
        if (m0 instanceof java.util.TreeMap)
            res = new java.util.TreeMap<S,U>();
        else if (m0 instanceof java.util.concurrent.ConcurrentHashMap)
            res = new java.util.concurrent.ConcurrentHashMap<S,U>(size);
        else if (m0 instanceof java.util.IdentityHashMap)
            res = new java.util.IdentityHashMap<S, U>(size);
        else if (m0 instanceof java.util.WeakHashMap)
            res = new java.util.WeakHashMap<S,U>(size);
        else res = new HashMap<S,U>(size);

        for (Entry<S, ? extends T> e: m0.entrySet()) {
            final U value = m1.get(e.getValue());
            if (value != null)
                res.put(e.getKey(), value);
        }
        return res;
    }


    // =======================================================
    // Methods operating on Strings
    // =======================================================

    /**
     * Separates the single directory entries in a filename.
     * The first element is an empty String iff the filename is absolute.
     * (For a Windows filename, it contains a drive letter and a colon).
     * Ignores double slashes and slashes at the end, removes references to the cwd.
     * E.g., "/home//daniel/./key/" yields {"","home","daniel","key"}.
     * Tries to automatically detect UNIX or Windows directory delimiters.
     * There is no check whether all other characters are valid for filenames.
     */
    static List<String> disectFilename(String filename){
        final char sep = File.separatorChar;
        List<String> res = new ArrayList<String>();
        // if filename contains slashes, take it as UNIX filename, otherwise Windows
        if (filename.indexOf("/") != -1) assert sep == '/' : "\""+filename+"\" contains both / and \\";
        else if (filename.indexOf("\\") != -1) assert sep == '\\': "\""+filename+"\" contains both / and \\";
        else {
            res.add(filename);
            return res;
        }
        int i = 0;
        while (i < filename.length()){
            int j = filename.indexOf(sep,i);
            if (j == -1){ // no slash anymore
                final String s = filename.substring(i, filename.length());
                if (!s.equals("."))
                    res.add(s);
                break;
            }
            if (i == j) {
                // empty string between slashes
                if (i == 0)
                    // leading slash
                    res.add("");
            } else {
                // contains "/./"
                final String s = filename.substring(i, j);
                if (!s.equals(".")) {
                    res.add(s);
                }
            }
            i = j+1;
        }
        return res;
    }

    /** Returns a filename relative to another one.
     * The second parameter needs to be absolute and is expected to refer to directory
     * This method only operates on Strings, not on real files!
     * Note that it treats Strings case-sensitive.
     * The resulting filename always uses UNIX directory delimiters.
     */
    public static String makeFilenameRelative(String origFilename, String toFilename){
        final List<String> origFileNameSections = disectFilename(origFilename);
        String[] a = origFileNameSections.toArray(new String[origFileNameSections.size()]);
        final List<String> destinationFilenameSections = disectFilename(toFilename);
        String[] b = destinationFilenameSections.toArray(new String[destinationFilenameSections.size()]);

        // check for Windows paths
        if (File.separatorChar == '\\' &&
                a[0].length() == 2 && a[0].charAt(1) == ':') {
            char drive = Character.toUpperCase(a[0].charAt(0));
            if (!(b[0].length() == 2 && Character.toUpperCase(b[0].charAt(0)) == drive && b[0].charAt(1) == ':'))
                throw new RuntimeException("cannot make paths on different drives relative");
            // remove drive letter
            a[0] = ""; b[0] = "";
        }
        int i;
        String s = "";
        String t = "";

        if (a[0].equals("")) { // not already relative
        if (!b[0].equals(""))
            throw new RuntimeException("\""+toFilename+ "\" is a relative path. Please use absolute paths to make others relative to them.");

        // remove ".." from paths
        a = removeDotDot(a);
        b = removeDotDot(b);

        // FIXME: there may be leading ..'s

        i = 1; boolean diff= false;
        while (i < b.length){
            // shared until i
            if (i >= a.length || !a[i].equals(b[i])) diff = true;
            // add ".." for each remaining element in b
            // and collect the remaining elements of a
            if (diff) {
                s = s + "../";
                if (i < a.length)
                    t = t + (a[i].equals("")? "" : "/")+ a[i];
            }
            i++;
        }
        } else { i = 0; }
        while (i < a.length)
            t = t +(a[i].equals("")? "" : "/")+ a[i++];
        // strip leading slash
        if (t.length()>0 && t.charAt(0) == '/')
            t = t.substring(1);
        // strip ending slash
        t = s + t;
        if (t.length() > 0 && t.charAt(t.length()-1) == '/')
            t = t.substring(0,t.length()-1);
        return t;
    }


    private static String[] removeDotDot(String[] a) {
        String[] newa = new String[a.length];
        int k = 0;
        for (int j = 0; j < a.length-1; j++){
            if (a[j].equals("..") || !a[j+1].equals("..")){
                newa[k++] = a[j];
            } else
                j++;
        }
        if (!a[a.length-1].equals("..")){
            newa[k++] = a[a.length-1];
        }
        return Arrays.copyOf(newa, k);
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

    /**
     * Join the string representations of a collection of objects into onw
     * string. The individual elements are separated by a delimiter.
     *
     * {@link Object#toString()} is used to turn the objects into strings.
     *
     * @param collection
     *            an arbitrary non-null collection
     * @param delimiter
     *            a non-null string which is put between the elements.
     *
     * @return the concatenation of all string representations separated by the
     *         delimiter
     */
    public static String join(Iterable<?> collection, String delimiter) {
        StringBuilder sb = new StringBuilder();
        for (Object obj : collection) {
            if(sb.length() > 0) {
                sb.append(delimiter);
            }
            sb.append(obj);
        }

        return sb.toString();
    }

    /**
     * Join the string representations of an array of objects into one
     * string. The individual elements are separated by a delimiter.
     *
     * {@link Object#toString()} is used to turn the objects into strings.
     *
     * @param collection
     *            an arbitrary non-null array of objects
     * @param delimiter
     *            a non-null string which is put between the elements.
     *
     * @return the concatenation of all string representations separated by the
     *         delimiter
     */
    public static String join(Object[] collection, String delimiter) {
        return join(Arrays.asList(collection), delimiter);
    }

    /**
     * Takes a string and returns a string which is potentially shorter and
     * contains a sub-collection of the original characters.
     *
     * All alphabetic characters (A-Z and a-z) are copied to the result while
     * all other characters are removed.
     *
     * @param string
     *            an arbitrary string
     * @return a string which is a sub-structure of the original character
     *         sequence
     *
     * @author mattias ulbrich
     */
    public static /*@NonNull*/ String filterAlphabetic(/*@NonNull*/ String string) {
        StringBuilder res = new StringBuilder();
        for (int i = 0; i < string.length(); i++) {
            char c = string.charAt(i);
            if((c >= 'A' && c <= 'Z') || (c >= 'A' && c <= 'Z')) {
                res.append(c);
            }
        }
        return res.toString();
    }

    /** Checks whether a string contains another one as a whole word
     * (i.e., separated by whitespaces or a semicolon at the end).
     * @param s string to search in
     * @param word string to be searched for
     */
    public static boolean containsWholeWord(String s, String word){
        if (s == null || word == null) return false;
        int i = -1;
        final int wl = word.length();
        while (true) {
            i = s.indexOf(word, i+1);
            if (i < 0 || i >= s.length()) break;
            if (i == 0 || Character.isWhitespace(s.charAt(i-1))) {
                if (i+wl == s.length() || Character.isWhitespace(s.charAt(i+wl)) || s.charAt(i+wl) == ';') {
                    return true;
                }
            }
        }
        return false;
    }


    /** There are different kinds of JML markers.
     * See Section 4.4 "Annotation markers" of the JML reference manual.
     * @param comment
     * @return
     */
    public static boolean isJMLComment(String comment) {
        try {
        return (comment.startsWith("/*@") || comment.startsWith("//@")
                || comment.startsWith("/*+KeY@") || comment.startsWith("//+KeY@")
                || (comment.startsWith("/*-")&& !comment.substring(3,6).equals("KeY") && comment.contains("@"))
                || (comment.startsWith("//-") && !comment.substring(3,6).equals("KeY") && comment.contains("@")));
        } catch (IndexOutOfBoundsException e){
            return false;
        }
    }

    /**
     * <p>
     * Returns the display name of the applied rule in the given {@link Node} of
     * the proof tree in KeY.
     * </p>
     * <p>
     * This method is required for the symbolic execution tree extraction,
     * e.g. used in the Symbolic Execution Tree Debugger.
     * </p>
     * @param node The given {@link Node}.
     * @return The display name of the applied rule in the given {@link Node} or {@code null} if no one exists.
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
     * This method is required for the symbolic execution tree extraction,
     * e.g. used in the Symbolic Execution Tree Debugger.
     * </p>
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
     * Returns the name of the applied rule in the given {@link Node} of
     * the proof tree in KeY.
     * </p>
     * <p>
     * This method is required for the symbolic execution tree extraction,
     * e.g. used in the Symbolic Execution Tree Debugger.
     * </p>
     * @param node The given {@link Node}.
     * @return The display name of the applied rule in the given {@link Node} or {@code null} if no one exists.
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
     * This method is required for the symbolic execution tree extraction,
     * e.g. used in the Symbolic Execution Tree Debugger.
     * </p>
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
     * @param proof The {@link Proof} to get its used {@link OneStepSimplifier}.
     * @return The used {@link OneStepSimplifier} or {@code null} if not available.
     */
    public static OneStepSimplifier findOneStepSimplifier(Proof proof) {
       if (proof != null && !proof.isDisposed()) {
          Profile profile = proof.env().getInitConfig().getProfile();
          return findOneStepSimplifier(profile);
       }
       else {
          return null;
       }
    }
    
    /**
     * Returns the {@link OneStepSimplifier} used in the given {@link Profile}.
     * @param profile The {@link Profile} to get its used {@link OneStepSimplifier}.
     * @return The used {@link OneStepSimplifier} or {@code null} if not available.
     */
    public static OneStepSimplifier findOneStepSimplifier(Profile profile) {
       if (profile instanceof JavaProfile) {
          return ((JavaProfile) profile).getOneStepSimpilifier();
       }
       else {
          return null;
       }
    }

    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------

    private static final class ReadPVCollector extends JavaASTVisitor {
	private ImmutableSet<ProgramVariable> result
		= DefaultImmutableSet.<ProgramVariable>nil();

	private ImmutableSet<ProgramVariable> declaredPVs
		= DefaultImmutableSet.<ProgramVariable>nil();

	public ReadPVCollector(ProgramElement root, Services services) {
	    super(root, services);
	}

	@Override
	protected void doDefaultAction(SourceElement node) {
	    if(node instanceof ProgramVariable) {
		ProgramVariable pv = (ProgramVariable) node;
		if(!pv.isMember() && !declaredPVs.contains(pv)) {
		    result = result.add(pv);
		}
	    } else if(node instanceof VariableSpecification) {
		VariableSpecification vs = (VariableSpecification) node;
		ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
		if(!pv.isMember()) {
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


    private static final class WrittenPVCollector extends JavaASTVisitor {
	private ImmutableSet<ProgramVariable> result
		= DefaultImmutableSet.<ProgramVariable>nil();

	private ImmutableSet<ProgramVariable> declaredPVs
		= DefaultImmutableSet.<ProgramVariable>nil();

	public WrittenPVCollector(ProgramElement root, Services services) {
	    super(root, services);
	}

	@Override
	protected void doDefaultAction(SourceElement node) {
	    if(node instanceof Assignment) {
		ProgramElement lhs = ((Assignment) node).getChildAt(0);
		if(lhs instanceof ProgramVariable) {
		    ProgramVariable pv = (ProgramVariable) lhs;
		    if(!pv.isMember() && !declaredPVs.contains(pv)) {
			result = result.add(pv);
		    }
		}
	    } else if(node instanceof VariableSpecification) {
		VariableSpecification vs = (VariableSpecification) node;
		ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
		if(!pv.isMember()) {
		    assert !declaredPVs.contains(pv);
		    assert !result.contains(pv);
		    declaredPVs = declaredPVs.add(pv);
		}
	    }
	}

	public ImmutableSet<ProgramVariable> result() {
	    return result;
	}
    }

    /**
     * read an input stream to its end into a string.
     *
     * @param is
     *            a non-null open input stream
     * @return the string created from the input of the stream
     * @throws IOException may occur while reading the stream
     */
    public static String toString(InputStream is) throws IOException {
        StringBuilder sb = new StringBuilder();
        byte[] buffer = new byte[2048];
        int read;
        while((read=is.read(buffer)) > 0) {
            sb.append(new String(buffer, 0, read));
        }
        return sb.toString();
    }
}
