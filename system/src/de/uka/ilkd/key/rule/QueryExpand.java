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

package de.uka.ilkd.key.rule;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;
import java.util.WeakHashMap;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;


/**
 * The QueryExpand rule allows to apply contracts or to symbolically execute a query
 * expression in the logic. It replaces the query expression by a new constant and
 * constructs a box formula in the antecedent 'defining' the constant as the result of
 * a method call. The method call is encoded directly as a method call in the box modality.
 * The query is invoked in a context equal to the container type of the query method.
 *
 * @author Richard Bubel
 */
public class QueryExpand implements BuiltInRule {

    public static final QueryExpand INSTANCE = new QueryExpand();

    private static final int DEFAULT_MAP_SIZE = 200;

    private static Name QUERY_DEF_NAME = new Name("Evaluate Query");

    private static final TermBuilder tb = TermBuilder.DF;

    /** Stores a number that indicates the time when term occurred for the first time where
     * this rule was applicable. The time is the number of rules applied on this branch.*/
    private WeakHashMap<Term,Long> timeOfTerm = new WeakHashMap<Term,Long>(DEFAULT_MAP_SIZE);


    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) {

        final PosInOccurrence pio = ruleApp.posInOccurrence();
        final Term query = pio.subTerm();

        // new goal
        ImmutableList<Goal> newGoal = goal.split(1);
        Goal g = newGoal.head();

        Pair<Term,Term> queryEval = queryEvalTerm(services, query, null);

        // The following additional rewrite taclet increases performance
        // (sometimes significantly, e.g. by factor 10).
        RewriteTacletBuilder tb = new RewriteTacletBuilder();
        Name tacletName = MiscTools.toValidTacletName("replaceKnownQuery_" + query.toString());
        tb.setName(tacletName);
        tb.setDisplayName("replaceKnownQuery");
        tb.setFind(query);
        tb.setApplicationRestriction(RewriteTaclet.IN_SEQUENT_STATE);
        tb.addGoalTerm(queryEval.second);
        tb.addRuleSet(new RuleSet(new Name("concrete")));

        g.addFormula(new SequentFormula(queryEval.first), true, true);	//move the query call directly to the succedent. Use box instead of diamond?
        g.addTaclet(tb.getTaclet(), SVInstantiations.EMPTY_SVINSTANTIATIONS, true);

        /*  replaces old query
        final Term newFormula = replace(pio.constrainedFormula().formula(),
                tb.func(placeHolderResult), pio.posInTerm().iterator());
        g.changeFormula(new SequentFormula(newFormula), pio.topLevel());
         */

        return newGoal;
    }

    /** Creates an invocation of a query in a modal operator and stores the value in a
     *  new symbol. This is a utility method, that may also be used by other classes.
     * @param services
     * @param query The query on which the query expand rule is applied
     * @param instVars If null, then the result of the query can be stored in a constant (e.g. res=query(a)).
     *        Otherwise it is a list of logical variables that can be instantiated (using the rules allLeft, exRight)
     *        and therefore the result of the query must be stored by function that depends on instVars (e.g. forall i; res(i)=query(i)).
     *        The list may be empty even if it not null.
     * @param newGoal The new goal that results from this rule application. (requires to register new symbols)
     * @return The formula (!{U}<result=query();>result=res_query) & query()=res_query
     * @author Richard Bubel
     * @author gladisch
     */
    public Pair<Term,Term> queryEvalTerm(Services services, Term query, LogicVariable[] instVars){

    	   final IProgramMethod method = (IProgramMethod)query.op();

           final ImmutableArray<ProgramVariable> args = getRegisteredArgumentVariables(method.getParameters(), services);


           //Names for additional symbols

           final String calleeName     = tb.newName(services, "callee");
           final String progResultName = tb.newName(services, "queryResult");
           final String logicResultName= tb.newName(services, "res_"+method.getName());
           //For declaring the symbol that stores the result in a logical term a trick is done.
           //The new symbolc is introduced as a logical variable that is later skolemized by the ex_left rule.
           //  LogicVariable logicResultQV = new LogicVariable(new Name("res_"+method.getName()),query.sort());

           KeYJavaType calleeType = services.getJavaInfo().getKeYJavaType(
             query.subs().size() == 1 ? // static query
                query.sort()
                :
                query.sub(1).sort());
           KeYJavaType progResultType = method.getReturnType();


           final ProgramVariable callee;
           final int offset;
           if (method.isStatic()) {
               callee = null;
               offset = 0;
           } else {
               callee = new LocationVariable(
                       new ProgramElementName(calleeName), calleeType);
               offset = 1;
           }

           final ProgramVariable result =
                   new LocationVariable(
                           new ProgramElementName(progResultName),
                                   progResultType);


           final MethodReference mr = new MethodReference(args, method.getProgramElementName(), callee);

           //final LocationVariable placeHoderResult = new LocationVariable(new ProgramElementName(logicResultName), logicResultType);
           //final Term placeHolderResultTrm = tb.var(logicResultQV);
           final Function placeHolderResult;
           final Term placeHolderResultTrm;

           if(instVars==null || instVars.length==0) {
        	   placeHolderResult    = new Function(new Name(logicResultName), query.sort());
        	   placeHolderResultTrm = tb.func(placeHolderResult);
           }else{ // If the query expansion depends on logical variables, then store the result in a function that depends on the logical variables.
        	   Term[] lvTrms = new Term[instVars.length];
        	   Sort[] lvSorts = new Sort[instVars.length];
        	   for(int i =0;i<instVars.length;i++){
        		   lvTrms[i] = tb.var(instVars[i]);
        		   lvSorts[i] = instVars[i].sort();
        	   }
        	   ImmutableArray<Sort> imArrlvSorts = new ImmutableArray<Sort>(lvSorts);
        	   placeHolderResult    = new Function(new Name(logicResultName), query.sort(), imArrlvSorts);
        	   placeHolderResultTrm = tb.func(placeHolderResult, lvTrms, null); //I'm not sure about the third parameter!
           }

           services.getNamespaces().functions().addSafely(placeHolderResult);

           // construct method call   {heap:=h || p1:arg1 || ... || pn:=argn}
           //                                  \[ res = o.m(p1,..,pn); \] (c = res)

           ArrayList<ProgramElement> stmnt = new ArrayList<ProgramElement>();

           stmnt.add(KeYJavaASTFactory.declare(result, progResultType));

           final CopyAssignment assignment = new CopyAssignment(result, mr);

           stmnt.add(assignment);

           StatementBlock s = new StatementBlock(stmnt.toArray(new Statement[stmnt.size()]));



           final MethodFrame mf = new MethodFrame(null,
                   new ExecutionContext(new TypeRef(method.getContainerType()), method, null),
                   //new StatementBlock(assignment)
                   s);
           final JavaBlock jb = JavaBlock.createJavaBlock(new StatementBlock(mf));

           final Term methodCall = tb.dia(jb, tb.not(tb.equals(tb.var(result),placeHolderResultTrm)));  //Not sure if box or diamond should be used.
           //final Term methodCall = tb.box(jb, tb.equals(tb.var(result), query));

           Term update = tb.elementary(services, services.getTypeConverter().getHeapLDT().getHeap(), query.sub(0));
           if (callee != null) {
               update = tb.parallel(tb.elementary(services, tb.var(callee), query.sub(1)), update);
           }

           final Term[] argUpdates = new Term[args.size()];
           for (int i = 0; i<args.size(); i++) {
               argUpdates[i] = tb.elementary(services, tb.var(args.get(i)), query.sub(offset+1+i));
           }

           update = tb.parallel(update, tb.parallel(argUpdates));

           Term topLevel = tb.not(tb.apply(update, methodCall, null));


           // The following additional equation increases performance (sometimes significantly, e.g. by factor 10).
           // CS: It is even more efficien to introduce a rewrite taclet instead
           // of an equation. Therefore return the placeHolderResultTrm such that
           // the caller can decide whether to introduce an equation or taclet.
//           topLevel = tb.and(topLevel, tb.equals(query,placeHolderResultTrm));

           //topLevel = tb.ex(logicResultQV, topLevel); //Alternative way to declare the symbol

           return new Pair<Term,Term>(topLevel, placeHolderResultTrm);
    }



    private ImmutableArray<ProgramVariable> getRegisteredArgumentVariables(
            ImmutableArray<ParameterDeclaration> paramDecls, Services services) {

        final Namespace progvarsNS = services.getNamespaces().programVariables();
        final ProgramVariable[] args = new ProgramVariable[paramDecls.size()];
        int i = 0;
        for (final ParameterDeclaration pdecl : paramDecls) {
        	final String baseName = pdecl.getVariableSpecification().getName();
        	final String newName = tb.newName(services,baseName);
            final ProgramElementName argVarName = new ProgramElementName(newName);
            args[i] = new LocationVariable(argVarName,
                    pdecl.getVariableSpecification().getProgramVariable().getKeYJavaType());
            progvarsNS.addSafely(args[i]);
            //newGoal.addProgramVariable(pv);
            i++;
        }

        return new ImmutableArray<ProgramVariable>(args);
    }


    /**
     * Apply "evaluate query" to the queries that occur in <code>term</code>. The query evaluations/expansions are inserted
     * into a copy of <code>term</code> that is returned.
     * @param services
     * @param term  A formula that potentially contains queries that should be evaluated/expanded.
     * @param positiveContext Set false iff the <code>term</code> is in a logically negated context wrt. to the succedent.
     * @param allowExpandBelowInstQuantifier TODO
     * @return A modified version of the <code>term</code> with inserted "query evalutions".
     * @author gladisch
     */
    public Term evaluateQueries(Services services,  Term term, boolean positiveContext, boolean allowExpandBelowInstQuantifier){
    	//System.out.println("---------- evaluateQueries on:  ---------------- "+term+"\n-------------------------------\n");
    	final int depth =term.depth();
    	List<QueryEvalPos> qeps = new Vector<QueryEvalPos>();
    	Vector<Integer> path = new Vector<Integer>(depth);
    	path.setSize(depth);
    	final ImmutableSLList<QuantifiableVariable> instVars;
    	if(allowExpandBelowInstQuantifier){
    		instVars = ImmutableSLList.nil();
    	}else{
    		instVars = null;
    	}
    	findQueriesAndEvaluationPositions(term, 0, path, instVars, positiveContext, 0, positiveContext, qeps);
    	removeRedundant(qeps);
    	//sorting is important in order to ensure that the original term is modified in a depth-first order.
    	Collections.sort(qeps);

    	for(QueryEvalPos qep: qeps){
    	    //System.out.println("\nInserting: "+qep+"\n");
        	Pair<Term,Term> queryExp = QueryExpand.INSTANCE.queryEvalTerm(services, qep.query, qep.instVars);
                Term queryExpTerm = tb.and(queryExp.first, tb.equals(qep.query,queryExp.second));
        	Iterator<Integer> it = qep.pathInTerm.iterator();
        	it.next(); //Skip the first element
        	final Term termToInsert;
        	if(qep.positivePosition){
        		termToInsert = tb.imp(queryExpTerm,qep.getTermOnPath(term));
        	}else{
        		termToInsert = tb.and(queryExpTerm,qep.getTermOnPath(term));
        	}
        	//System.out.println("----------- Calling replace. Insert term: ----------------\n"+termToInsert+"\n-----------------------\n");
        	//Attention, when the term is modified, then the paths in the term have changed. Perform the changes in a depth-first order.
        	term = replace(term, termToInsert, it);
    	}
        	//TermBuilder TB = TermBuilder.DF;
        	//result = TB.and( queryExp, term);
    	return term;
    }


    /** Find queries in t and suitable positions where to insert their evaluations in t.
     * This method is called by the method <code>evaluateQueries<\code>.
     * @param t The term where to search for queries and query evaluation positions.
     * @param level The current recursion level of this method call.
     * @param pathInTerm Vector of integers describing the current path in the syntax tree (of the term at level 0).
     * @param instVars If null, then query evaluation below instantiable quantifiers (i.e. non-Skolemizable quantifiers) is suppressed.
     *         If not null, then this list collects the logical variables of instantiable quantifers that the query evaluation depends on.
     *         This is to needed to create e.g. (forall i; query(i)=res(i)) instead of (forall i;query(i)=res); the latter is unsound.
     * @param curPosIsPositive True iff the current position in the formula we are in is a logically positive context (when considering polarity wrt. logical negation).
     * @param qepLevel The top-most level on the current path where the query evaluation could be inserted. Its either top-level (0) or below a quantifier.
     * @param qepIsPositive True iff the logical context at position qepLevel is positive (i.e., not negated, or negations have cancelled out).
     * @param qeps The resulting collection of query evaluation positions.
     * @author gladisch
     */
    @SuppressWarnings("unchecked")
    private void findQueriesAndEvaluationPositions(Term t, int level, Vector<Integer> pathInTerm,
    		               ImmutableList<QuantifiableVariable> instVars, boolean curPosIsPositive,
    		               int qepLevel, boolean qepIsPositive, List<QueryEvalPos> qeps){
    	if(t==null){
    		return;
    	}
    	final Operator op = t.op();
    	final int nextLevel = level+1;
    	if(op instanceof IProgramMethod && !((IProgramMethod)op).isModel()){ //Query found
    		//System.out.println("Query found:"+t+ " position:"+(qepIsPositive?"positive":"negative"));
    		QueryEvalPos qep = new QueryEvalPos(t, (Vector<Integer>)pathInTerm.clone(), qepLevel+1, instVars, qepIsPositive);
    		qeps.add(qep);
    		//System.out.println("AddedA: "+qep);
    		return;
    	}else if(op== Junctor.AND || op== Junctor.OR){
    		pathInTerm.set(nextLevel, 0);
    		findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars, curPosIsPositive, qepLevel, qepIsPositive, qeps);
    		pathInTerm.set(nextLevel, 1);
    		findQueriesAndEvaluationPositions(t.sub(1), nextLevel, pathInTerm, instVars, curPosIsPositive, qepLevel, qepIsPositive, qeps);
    	}else if(op== Junctor.IMP){
    		pathInTerm.set(nextLevel, 0);
    		findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars, !curPosIsPositive, qepLevel, qepIsPositive, qeps);
    		pathInTerm.set(nextLevel, 1);
    		findQueriesAndEvaluationPositions(t.sub(1), nextLevel, pathInTerm, instVars, curPosIsPositive, qepLevel, qepIsPositive, qeps);
    	}else if(op== Junctor.NOT){
    		pathInTerm.set(nextLevel, 0);
    		findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars, !curPosIsPositive, qepLevel, qepIsPositive, qeps);
    	}else if(op== Equality.EQV){
    		// Each subformula of "<->" is in both, positive and negative scope. Query expansion below it would be unsound.
    		// Alternatively "<->" could be converted into "->" and "<-"
    		return;
    	}else if(t.javaBlock()!=JavaBlock.EMPTY_JAVABLOCK){ //do not descend below java blocks.
    		return;
    	}else if(op== Quantifier.ALL ){
    		if(curPosIsPositive){ //Quantifier that will be Skolemized
    			//This is a potential query evaluation position.
        		pathInTerm.set(nextLevel, 0);
    			findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars, curPosIsPositive, nextLevel, curPosIsPositive, qeps);
    		}else{ //Quantifier that will be instantiated. Warning: this may explode!
    			if(instVars!=null){
    			   pathInTerm.set(nextLevel, 0);
        		   assert t.boundVars().get(0) instanceof LogicVariable;
        		   instVars = instVars.append(t.boundVars());
    			   findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars, curPosIsPositive, nextLevel, curPosIsPositive, qeps);
    			}
    		}
    	}else if(op== Quantifier.EX ){
    		if(curPosIsPositive){ //Quantifier that will be instantiated. Warning: this may explode!
    			if(instVars!=null){
        		   pathInTerm.set(nextLevel, 0);
        		   assert t.boundVars().get(0) instanceof LogicVariable;
        		   instVars = instVars.append(t.boundVars());
    			   findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars, curPosIsPositive, nextLevel, curPosIsPositive, qeps);
    			}
    		}else{ //Quantifier that will be Skolemized
    			//This is a potential query evaluation position.
        		pathInTerm.set(nextLevel, 0);
    			findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, instVars, curPosIsPositive, nextLevel, curPosIsPositive, qeps);
    		}
    	}else if(t.sort() == Sort.FORMULA){
    		Vector<Term> queries = collectQueries(t);
    		for(Term query:queries){
        		QueryEvalPos qep = new QueryEvalPos(query, (Vector<Integer>)pathInTerm.clone(), qepLevel+1, instVars, qepIsPositive);
        		qeps.add(qep);
        		//System.out.println("AddedB: "+qep);
    		}
    	}
    }


    private Vector<Term> collectQueries(Term t){
    	Vector<Term> queries = new Vector<Term>();
    	collectQueriesRecursively(t,queries);
    	return queries;
    }


    /** Utility method called by <code>collectQueriesRecursively</code> */
    private void collectQueriesRecursively(Term t, Vector<Term> result){
    	if(t.javaBlock()!=JavaBlock.EMPTY_JAVABLOCK){
    		//System.out.println("collectQueriesRec encountered javaBlock.");
    		return;
    	}
    	// What about checking if an update is encountered?

    	if(t.op() instanceof IProgramMethod && !((IProgramMethod)t.op()).isModel()){ //Query found
    		//System.out.println("Query found:"+t);
    		result.add(t);
    		return;
    	}else{
    		for(int i=0;i<t.arity();i++){
    			collectQueriesRecursively(t.sub(i),result);
    		}
    	}
    }


    /**
     * Tries to remove redundant query evaluations/expansions.
     */
    private void removeRedundant(List<QueryEvalPos> qeps){
    	int size=qeps.size();
    	for(int i=0;i<size;i++){
    		QueryEvalPos cur = qeps.get(i);
    		for(int k=0;k<size;k++){
    			QueryEvalPos other = qeps.get(k);
    			if(i!=k && cur.subsumes(other)){
    				qeps.remove(k);
    				//System.out.println("Removed:"+other);
    				size--;
    			}
    		}
    	}
    }


    /**
     * Query evaluation position. Describes where to insert a query evaluation/expansion (see <code>QueryExpand</code>)
     * in a formula.
     * @author gladisch
     */
    private class QueryEvalPos implements Comparable<QueryEvalPos> {

    	/** The query that is subject to query evaluation/expansion.
    	 * The query itself is not modified but a formula is added at a position
    	 * described by the other fields. */
    	final public Term query;
    	/** Positive or negative position wrt. logical negation. 	 */
    	final public boolean positivePosition;
    	/** Path in the syntax tree of the term where the query evaluation/expansion should be inserted.
    	 *  The first element has no meaning and should be null. The path starts with the second element. */
    	final public Vector<Integer> pathInTerm;

    	final public LogicVariable[] instVars;

    	@SuppressWarnings("unchecked")
        public QueryEvalPos(Term query, Vector<Integer> path, int level, ImmutableList<QuantifiableVariable> iVars, boolean isPositive){
    		this.query = query;
    		pathInTerm = (Vector<Integer>)path.clone();
			pathInTerm.setSize(level);
			positivePosition = isPositive;
			if(iVars!=null){
				instVars = new LogicVariable[iVars.size()];
				iVars.toArray(instVars);
			}else{
				instVars = new LogicVariable[0];
			}
    	}


    	public String toString(){
    		String pathstr = "[";
    		for(Integer in:pathInTerm){
    			pathstr += in+", ";
    		}
    		pathstr+="]";
    		return "QueryEvalPos of "+ (query!=null?query.toString():"NOQUERY")+
    				" in "+(positivePosition?"positive":"negative")+" position " +
    				(instVars.length>0?"  instVar:"+instVars[0]+" ":"") +
    				" insertPath:"+pathstr;
    	}

    	public Term getTermOnPath(Term root){
    		Term result = root;
    		for(int i=1 /*skip the first*/;i<pathInTerm.size();i++){
    			result = result.sub(pathInTerm.get(i));
    		}
    		return result;
    	}


    	public boolean subsumes(QueryEvalPos other){
    		if(!query.equals(other.query) || pathInTerm.size()>other.pathInTerm.size() ||
    				!Arrays.deepEquals(instVars, other.instVars)) {
    			return false;
    		}
    		//query.equals(other.query) && pathInTerm.size()<=other.pathInTerm.size()
    		for(int i=0;i<pathInTerm.size();i++){
    			if(pathInTerm.get(i)!=other.pathInTerm.get(i)){
    				//System.out.println("Same term but different paths");
    				return false;
    			}
    		}
    		return true;
    	}

    	/** For sorting. Longer paths come first in order to apply
    	 * modifications to the target term in a depth-first order.	 */
		@Override
		public int compareTo(QueryEvalPos other) {
			final int otherSize = other.pathInTerm.size();
			final int thisSize  = pathInTerm.size();
			return (thisSize<otherSize? 1 : (thisSize>otherSize? -1 : 0));
		}
    }


    /**
     * Replaces in a term.
     * @param term
     * @param with
     * @param it iterator with argument positions. This is the path in the syntax tree of term.
     * @return Resulting term after replacement.
     * @note Was originally implemented in QueryExpand.java.
     */
    protected Term replace(Term term, Term with, Iterator<Integer> it) {
        if ( !it.hasNext() ) {
            return with;
        }

        final int arity = term.arity();
        final Term newSubTerms[] = new Term[arity];
        boolean changedSubTerm = false;
        int next = (Integer)(it.next());
        //System.out.print(next+", ");
        for(int i = 0; i < arity; i++) {
            Term subTerm = term.sub(i);
            if (i == next) {
                newSubTerms[i] = replace(subTerm, with, it);
                if(newSubTerms[i] != subTerm) {
                    changedSubTerm = true;
                }
            } else {
                newSubTerms[i] = subTerm;
            }

        }

        final ImmutableArray<QuantifiableVariable> newBoundVars = term.boundVars();

        final Term result;
        if(changedSubTerm) {
            result = TermFactory.DEFAULT.createTerm(term.op(),
                    newSubTerms,
                    newBoundVars,
                    term.javaBlock());
        } else {
            result = term;
        }

        return result;
    }


    @Override
    public Name name() {
        return QUERY_DEF_NAME;
    }

    @Override
    public String displayName() {
        return QUERY_DEF_NAME.toString();
    }

    @Override
    public String toString() {
        return displayName();
    }

    @Override
    /**
     * Important the correctness of the implementation of this rule relies on the following side-conditions:
     * <ul>
     * <li>the query term has no free variables</li>
     * <li>the query term does not occur below an update or a modality</li>
     * </ul>
     * If you want to change this you need to adapt the application logic by adding preceding updates in front of the new added formula and/or
     * to take care of free variables when introducing the skolemfunction symbol and when replacing the query term by the skolem function.
     *
     * The method is equipped with a side-effect that stores the age of the term. This information is useful
     * for <code>QueryExpandCost</cost>.
     */
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio != null
                && pio.subTerm().op() instanceof IProgramMethod
                && pio.subTerm().freeVars().isEmpty()) {
            final Term pmTerm = pio.subTerm();
            IProgramMethod pm = (IProgramMethod) pmTerm.op();
            if(pm.isModel()) {
              return false;
            }
            // abort if inside of transformer
            if (Transformer.inTransformer(pio)) {
                return false;
            }
            final Sort nullSort = goal.proof().getJavaInfo().nullSort();
            if (pm.isStatic()
                    || (pmTerm.sub(1).sort().extendsTrans(goal.proof().getJavaInfo().objectSort())
                            && !pmTerm.sub(1).sort().extendsTrans(nullSort))) {
                PIOPathIterator it = pio.iterator();
                while ( it.next() != -1 ) {
                    Term focus = it.getSubTerm();
                    if (focus.op() instanceof UpdateApplication || focus.op() instanceof Modality) {
                        return false;
                    }
                }
                storeTimeOfQuery(pio.subTerm(), goal);
                return true;
            }
        }
        return false;
    }

    private void storeTimeOfQuery(Term query, Goal goal){
    	if(timeOfTerm.get(query)==null){
    		timeOfTerm.put(query, goal.getTime());
    	}
    }

    public Long getTimeOfQuery(Term t){
    	if(t==null || !(t.op() instanceof IProgramMethod)){
    		System.err.println("QueryExpand::getAgeOfQuery(t). The term is expected to be a query but it is:"+(t!=null?t:"null"));
    		return null;
    	}
    	return timeOfTerm.get(t);

    }

	@Override
    public DefaultBuiltInRuleApp createApp(PosInOccurrence pos) {
	    return new DefaultBuiltInRuleApp(this, pos);
    }


}
