// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.util;

import java.io.File;
import java.util.*;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.*;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.*;


/**
 * Collection of some common, stateless functionality. Stolen from
 * the weissInvariants side branch.
 */
public final class MiscTools {
       
    private static final TermBuilder TB = TermBuilder.DF;
    
    private MiscTools() {}
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    /**
     * Removes universal quantifiers from a formula.
     */
    public static Term open(Term formula) {
	assert formula.sort() == Sort.FORMULA;
	if(formula.op() == Quantifier.ALL) {
	    return open(formula.sub(0)); 
	} else {
	    return formula;
	}
    }
    
    
    /**
     * Returns the set of elementary conjuncts of the passed formula.
     */
    public static ImmutableSet<Term> toSet(Term formula) {
	assert formula.sort().equals(Sort.FORMULA);
	ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        ImmutableList<Term> workingList 
        	= ImmutableSLList.<Term>nil().prepend(formula);
        while(!workingList.isEmpty()) {
            final Term f = workingList.head();
            workingList = workingList.tail();
            if(f.op() == Junctor.AND) {
                workingList = workingList.prepend(f.sub(1)).prepend(f.sub(0));
            } else {
                result = result.add(f);
            }
        }
        return result;
    }
    
    
    public static ImmutableSet<Term> unionToSet(Term s, Services services) {
	final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
	assert s.sort().equals(setLDT.targetSort());
	final Function union = setLDT.getUnion();
	ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        ImmutableList<Term> workingList = ImmutableSLList.<Term>nil().prepend(s);
        while(!workingList.isEmpty()) {
            Term f = workingList.head();
            workingList = workingList.tail();
            if(f.op() == union) {
                workingList = workingList.prepend(f.sub(1)).prepend(f.sub(0));
            } else {
                result = result.add(f);
            }
        }
        return result;
    }
    

    /**
     * Conjoins the formulas in the passed set.
     */
    public static Term toFormula(ImmutableSet<Term> set) {
	Term result = TB.tt();
	for(Term term : set) {
	    result = TB.and(result, term);
	}
	return result;
    }

    
    /**
     * Returns the active statement of the passed a java block.
     */
    public static SourceElement getActiveStatement(JavaBlock jb) {
	assert jb.program() != null;
	
        SourceElement result = jb.program().getFirstElement();
        while((result instanceof ProgramPrefix 
        	 || result instanceof CatchAllStatement)
              && !(result instanceof StatementBlock 
                   && ((StatementBlock)result).isEmpty())) {
            if(result instanceof LabeledStatement) {
                result = ((LabeledStatement)result).getChildAt(1);
            } else if(result instanceof CatchAllStatement) {
        	result = ((CatchAllStatement)result).getBody();
            } else {
                result = result.getFirstElement();
            }
        }
        return result;
    }
    
    
    /**
     * Returns the passed java block without its active statement.
     */
    public static JavaBlock removeActiveStatement(JavaBlock jb, 
	    					  Services services) {
        assert jb.program() != null;
        final SourceElement activeStatement = getActiveStatement(jb);
        Statement newProg = (Statement)
            (new CreatingASTVisitor(jb.program(), false, services) {
                private boolean done = false;
                
                public ProgramElement go() {
                    stack.push(new ExtList());
                    walk(root());
                    ExtList el = stack.peek();
                    return el.get(ProgramElement.class); 
                }
                
                public void doAction(ProgramElement node) {
                    if(!done && node == activeStatement) {
                        done = true;
                        stack.pop();                    
                        changed();
                    } else {
                        super.doAction(node);
                    }
                }
            }).go();
        
        StatementBlock newSB = newProg instanceof StatementBlock 
                               ? (StatementBlock)newProg
                               : new StatementBlock(newProg);              
        return JavaBlock.createJavaBlock(newSB);
    }
    
    
    /**
     * Returns the innermost method frame of the passed java block
     */
    public static MethodFrame getInnermostMethodFrame(JavaBlock jb, 
	    				       	      Services services) { 
        final ProgramElement pe = jb.program();
        final MethodFrame result = new JavaASTVisitor(pe, services) {
            private MethodFrame res;
            protected void doAction(ProgramElement node) {
                node.visit(this);
            }
            protected void doDefaultAction(SourceElement node) {
                if(node instanceof MethodFrame && res == null) {
                    res = (MethodFrame) node;
                }
            }
            public MethodFrame run() {
                walk(pe);
                return res;
            }
        }.run();
                
        return result;
    }
    
    
    public static ExecutionContext getInnermostExecutionContext(
	    						JavaBlock jb, 
	    						Services services) {
	final MethodFrame frame = getInnermostMethodFrame(jb, services);
	return frame == null 
               ? null
	       : (ExecutionContext) frame.getExecutionContext();	
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
    
    
    /**
     * Removes all formulas from the passed goal.
     */
    public static void clearGoal(Goal goal) {
	for(SequentFormula cf : goal.sequent().antecedent()) {
            PosInOccurrence pio = new PosInOccurrence(cf, 
                                                      PosInTerm.TOP_LEVEL, 
                                                      true);
            goal.removeFormula(pio);
        }
	for(SequentFormula cf : goal.sequent().succedent()) {
            PosInOccurrence pio = new PosInOccurrence(cf, 
                                                      PosInTerm.TOP_LEVEL, 
                                                      false);
            goal.removeFormula(pio);
        }
    }
    
    
    /**
     * Tells whether the passed rule belongs to the specified rule set. 
     */
    public static boolean belongsTo(Rule rule, String ruleSetName) {	
        if(rule instanceof Taclet) {
    	    if(ruleSetName.endsWith("*")) {
    		ruleSetName 
    			= ruleSetName.substring(0, ruleSetName.length() - 1);
                for(RuleSet rs : ((Taclet)rule).getRuleSets()) {
                    if(rs.toString().startsWith(ruleSetName)) {
                        return true;
                    }
                }    	    
    	    } else {
                for(RuleSet rs : ((Taclet)rule).getRuleSets()) {
                    if(rs.toString().equals(ruleSetName)) {
                        return true;
                    }
                }
    	    }
        }
        return false;
    }
    

    /**
     * Tells whether the passed rule belongs to one of the specified rule sets.
     */
    public static boolean belongsTo(Rule rule, String[] ruleSetNames) {
        for(int i = 0; i < ruleSetNames.length; i++) {
            if(belongsTo(rule, ruleSetNames[i])) {
                return true;
            }
        }
        return false;
    }
    
    
    /**
     * Tells whether the passed rule is one of those specified by the second
     * argument.
     */
    public static boolean isOneOf(Rule rule, String[] ruleNames) {
	String s = rule.name().toString();
	for(int i = 0; i < ruleNames.length; i++) {
	    if(s.equals(ruleNames[i])) {
		return true;
	    }
	}
	return false;
    }
    
    
    /**
     * Removes leading updates from the passed term.
     */
    public static Term goBelowUpdates(Term term) {
        while(term.op() instanceof UpdateApplication) {
            term = UpdateApplication.getTarget(term);
        }        
        return term;
    }
    
    
    /**
     * Removes leading updates from the passed term.
     */
    public static Pair<ImmutableList<Term>,Term> goBelowUpdates2(Term term) {
	ImmutableList<Term> updates = ImmutableSLList.<Term>nil();
        while(term.op() instanceof UpdateApplication) {
            updates = updates.append(UpdateApplication.getUpdate(term));
            term = UpdateApplication.getTarget(term);
        }        
        return new Pair<ImmutableList<Term>,Term>(updates, term);
    }    
    
    
    /**
     * Returns the entry node for the innermost loop of the symbolic 
     * execution state given by the passed node.
     */
    public static Node getEntryNodeForInnermostLoop(Node node) {
        ImmutableList<LoopStatement> leftLoops 
            = ImmutableSLList.<LoopStatement>nil();
        for(Node n = node.parent(); n != null; n = n.parent()) {
            RuleApp app = n.getAppliedRuleApp();
            Rule rule = app.rule();
            if(belongsTo(rule, "loop_expand")) {
                Term progTerm 
                    = goBelowUpdates(app.posInOccurrence().subTerm());
                LoopStatement loop 
                    = (LoopStatement) getActiveStatement(progTerm.javaBlock());
                
                //left?
                boolean alreadyLeft = false;
                for(LoopStatement leftLoop : leftLoops) {
                    if(leftLoop.equalsModRenaming(loop, 
                                                  new NameAbstractionTable())) {
                        alreadyLeft = true;
                        break;
                    }
                }
                if(!alreadyLeft) {
                    return n;
                }
            } else if(rule == WhileInvariantRule.INSTANCE) {
                Term progTerm 
                    = goBelowUpdates(app.posInOccurrence().subTerm());
                LoopStatement loop 
                    = (LoopStatement) getActiveStatement(progTerm.javaBlock());
                leftLoops = leftLoops.prepend(loop);
            }
        }
        return null;
    }
    
    
    /**
     * Returns the entry node for the passed loop and the symbolic execution
     * state given by the passed node.
     */
    public static Node getEntryNodeForLoop(Node node, LoopStatement loop) {
        for(Node n = node.parent(); n != null; n = n.parent()) {            
            RuleApp app = n.getAppliedRuleApp();
            Rule rule = app.rule();
            if(belongsTo(rule, "loop_expand")) {
                Term progTerm 
                    = goBelowUpdates(app.posInOccurrence().subTerm());
                LoopStatement l 
                    = (LoopStatement) getActiveStatement(progTerm.javaBlock());
                if(loop.equalsModRenaming(l, new NameAbstractionTable())) {
                    return n;
                }
            } else if(rule == WhileInvariantRule.INSTANCE) {
                Term progTerm 
                    = goBelowUpdates(app.posInOccurrence().subTerm());
                LoopStatement l 
                    = (LoopStatement) getActiveStatement(progTerm.javaBlock());
                if(loop.equalsModRenaming(l, new NameAbstractionTable())) {
                    return null;
                }                
            }
        }
        return null;
    }
    
    
    /**
     * Tells whether the passed sets of location symbols are disjoint.
     */
    public static boolean areDisjoint(ImmutableSet<UpdateableOperator> set1, 
	    			      ImmutableSet<UpdateableOperator> set2) {
	for(UpdateableOperator loc : set1) {
            if(set2.contains(loc)) {
                return false;
            }
        }
        return true;
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
    
    
    public static ImmutableSet<Pair<Sort,ObserverFunction>> 
    						collectObservers(Term t) {
	ImmutableSet<Pair<Sort, ObserverFunction>> result 
		= DefaultImmutableSet.nil();
	if(t.op() instanceof ObserverFunction) {
	    final ObserverFunction obs = (ObserverFunction)t.op();
	    final Sort s = obs.isStatic() 
	             	   ? obs.getContainerType().getSort() 
	                   : t.sub(1).sort();
	    result = result.add(new Pair<Sort,ObserverFunction>(s, obs));	    
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
        String[] a = disectFilename(origFilename).toArray(new String[0]);
        String[] b = disectFilename(toFilename).toArray(new String[0]);
        
        // check for Windows paths
        if (a[0].length() == 2 && a[0].charAt(1) == ':') {
            // FIXME: UNIX filenames may well contain colons, too
            char drive = Character.toUpperCase(a[0].charAt(0));
            if (!(b[0].length() == 2 && Character.toUpperCase(b[0].charAt(0)) == drive && b[0].charAt(1) == ':'))
                throw new RuntimeException("cannot make paths on different drives relative");
            // remove drive letter
            a[0] = ""; b[0] = "";
        }
        
        if (!a[0].equals("")){ // already relative
            String res = "";
            for (String s: a){
                res += s;
            }
            return res;
        }
        if (!b[0].equals("")) 
            throw new RuntimeException("\""+toFilename+ "\" is a relative path. Please use absolute paths to make others relative to them.");
        
        // remove ".." from paths
        a = removeDotDot(a);
        b = removeDotDot(b);
        
        // FIXME: there may be leading ..'s
        
        int i = 1; boolean diff= false;
        String s = "";
        String t = "";
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
}
