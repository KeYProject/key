package de.uka.ilkd.key.rule;

import java.util.Collections;
import java.util.Iterator;
import java.util.Vector;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.VariableNameProposer;


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

    private static Name QUERY_DEF_NAME = new Name("Evaluate Query");

    private static final TermBuilder tb = TermBuilder.DF;


    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) {

        final PosInOccurrence pio = ruleApp.posInOccurrence();
        final Term query = pio.subTerm();

        // new goal
        ImmutableList<Goal> newGoal = goal.split(1);
        Goal g = newGoal.head();

        Term topLevel = queryEvalTerm(services, goal.node(), g, query);

        g.addFormula(new SequentFormula(topLevel), true, true);	//move the query call directly to the succedent. Use box instead of diamond?

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
     * @param node The node of the old goal.
     * @param newGoal The new goal that results from this rule application. (requires to register new symbols)
     * @param query The query on which the query expand rule is applied
     * @return The formula (!{U}<result=query();>result=res_query) & query()=res_query
     * @author Richard Bubel
     * @author gladisch 
     */
    public Term queryEvalTerm(Services services, Node node, Goal newGoal, Term query){
    	
    	   final ProgramMethod method = (ProgramMethod)query.op();


           final ImmutableArray<ProgramVariable> args = getArgumentVariables(method.getParameters(), node, services);
           
           //Names for additional symbols
           	final VariableNameProposer vnp = VariableNameProposer.DEFAULT;
          
           final String calleeName     = vnp.getNameProposal("callee", services, node);
           final String progResultName = vnp.getNameProposal("result", services, node);
           final String logicResultName= vnp.getNameProposal("res_"+method.getName(), services, node);
           
           final ProgramVariable callee;
           final int offset;
           if (method.isStatic()) {
               callee = null;
               offset = 0;
           } else {
               callee = new LocationVariable(
                       new ProgramElementName(calleeName),
                               services.getJavaInfo().getKeYJavaType(query.sub(1).sort()));
               offset = 1;
           }

           final ProgramVariable result = 
                   new LocationVariable(
                           new ProgramElementName(progResultName), 
                                   method.getReturnType());


           final MethodReference mr = new MethodReference(args, method.getProgramElementName(), callee);
           final Function placeHolderResult = new Function(new Name(logicResultName), query.sort());

           // construct method call   {heap:=h || p1:arg1 || ... || pn:=argn} 
           //                                  \[ res = o.m(p1,..,pn); \] (c = res) 

           final CopyAssignment assignment = new CopyAssignment(result, mr);
           final MethodFrame mf = new MethodFrame(null, 
                   new ExecutionContext(new TypeRef(method.getContainerType()), null),
                   new StatementBlock(assignment));
           final JavaBlock jb = JavaBlock.createJavaBlock(new StatementBlock(mf));	

           final Term methodCall = tb.dia(jb, tb.not(tb.equals(tb.var(result),tb.func(placeHolderResult))));  //Not sure if box or diamond should be used.
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

           Term topLevel = tb.not(tb.apply(update, methodCall));

           // chrisg: the following additional equation increases performance (sometimes significantly, e.g. by factor 10). 
           topLevel = tb.and(topLevel, tb.equals(query,tb.func(placeHolderResult)));
           
           //register variables in namespace
           for (final ProgramVariable pv : args) { // add new program variables for arguments
               newGoal.addProgramVariable(pv);
           }	
           if (callee != null) { newGoal.addProgramVariable(callee); }
           newGoal.addProgramVariable(result);
           services.getNamespaces().functions().add(placeHolderResult);

           return topLevel;
    }

    
    
    private ImmutableArray<ProgramVariable> getArgumentVariables(
            ImmutableArray<ParameterDeclaration> paramDecls, Node n, Services services) {

        final ProgramVariable[] args = new ProgramVariable[paramDecls.size()];
        int i = 0;
        for (final ParameterDeclaration pdecl : paramDecls) {
            final ProgramElementName argVarName = 
                    new ProgramElementName(VariableNameProposer.DEFAULT.
                            getNameProposal(pdecl.getVariableSpecification().getName(), services, n));

            args[i] = new LocationVariable(argVarName, 
                    pdecl.getVariableSpecification().getProgramVariable().getKeYJavaType());
            i++;
        }

        return new ImmutableArray<ProgramVariable>(args);
    }

    
    /** 
     * Apply "evaluate query" to the queries that occur in term. The query evaluations/expansions are inserted 
     * into a copy of term that is returned. 
     * @param services
     * @param node   The node of the current goal in the proof
     * @param newGoal The new goal that will result from query evaluation. This is needed to register new symbols.
     * @param term  A formula that potentially contains queries that should be evaluated/expanded.
     * @return A modified version of the <code>term</code> with inserted "query evalutions".
     * @author gladisch
     */
    public Term evaluateQueries(Services services, Node node, Goal newGoal, Term term){
    	System.out.println("---------- evaluateQueries on:  ---------------- "+term+"\n-------------------------------\n");
    	final int depth =term.depth(); 
    	Vector<QueryEvalPos> qeps = new Vector<QueryEvalPos>();
    	Vector<Integer> path = new Vector<Integer>(depth);
    	path.setSize(depth);
    	findQueriesAndEvaluationPositions(term, 0, path, true, 0, true, qeps);
    	final Term result;
    	//QueryEvalPos qep = qeps.get(7);

    	removeRedundant(qeps);
    	//sorting is important in order to ensure that the original term is modified in a depth-first order.
    	Collections.sort(qeps);

    	for(QueryEvalPos qep: qeps){
    	System.out.println("\nInserting: "+qep+"\n");
        	Term queryExp = QueryExpand.INSTANCE.queryEvalTerm(services, node, newGoal, qep.query);
        	Iterator<Integer> it = qep.pathInTerm.iterator();
        	it.next(); //Skip the first element
        	final Term termToInsert;
        	if(qep.positivePosition){
        		termToInsert = tb.imp(queryExp,qep.getTermOnPath(term));
        	}else{
        		termToInsert = tb.and(queryExp,qep.getTermOnPath(term));
        	}
        	System.out.println("----------- Calling replace. Insert term: ----------------\n"+termToInsert+"\n-----------------------\n");
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
     * @param curPosIsPositive True iff a the current position in the formula we are in a logically positive context (when considering logical negation). 
     * @param qepLevel The top-most level on the current path where the query evaluation could be inserted. Its either top-level (0) or below a quantifier.
     * @param qepIsPositive True iff the logical context at position qepLevel is positive (i.e., not negated, or negations have cancelled out).
     * @param qeps The resulting collection of query evaluation positions.
     * @author gladisch 
     */
    private void findQueriesAndEvaluationPositions(Term t, int level, Vector<Integer> pathInTerm, 
    		               boolean curPosIsPositive, int qepLevel, 
    		               boolean qepIsPositive, Vector<QueryEvalPos> qeps){
    	if(t==null){
    		return;
    	}
    	final Operator op = t.op();
    	final int nextLevel = level+1;
    	if(op instanceof ProgramMethod){ //Query found
    		//System.out.println("Query found:"+t+ " position:"+(positive?"positive":"negative"));
    		QueryEvalPos qep = new QueryEvalPos(t, (Vector<Integer>)pathInTerm.clone(), qepLevel+1, qepIsPositive);
    		qeps.add(qep);
    		System.out.println("AddedA: "+qep);
    		return;
    	}else if(op== Junctor.AND || op== Junctor.OR){
    		pathInTerm.set(nextLevel, 0);
    		findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, curPosIsPositive, qepLevel, qepIsPositive, qeps);
    		pathInTerm.set(nextLevel, 1);
    		findQueriesAndEvaluationPositions(t.sub(1), nextLevel, pathInTerm, curPosIsPositive, qepLevel, qepIsPositive, qeps);
    	}else if(op== Junctor.IMP){
    		pathInTerm.set(nextLevel, 0);
    		findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, !curPosIsPositive, qepLevel, qepIsPositive, qeps);
    		pathInTerm.set(nextLevel, 1);
    		findQueriesAndEvaluationPositions(t.sub(1), nextLevel, pathInTerm, curPosIsPositive, qepLevel, qepIsPositive, qeps);
    	}else if(op== Junctor.NOT){
    		pathInTerm.set(nextLevel, 0);
    		findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, !curPosIsPositive, qepLevel, qepIsPositive, qeps);
    	}else if(t.javaBlock()!=JavaBlock.EMPTY_JAVABLOCK){ //do not descend below java blocks.
    		return;
    	}else if(op== Quantifier.ALL ){ 
    		if(curPosIsPositive){ //Quantifier that will be Skolemized
    			//This is a potential query evaluation position. 
        		pathInTerm.set(nextLevel, 0);
    			findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, curPosIsPositive, nextLevel, curPosIsPositive, qeps);
    		}else{ //Quantifier that will be instantiated. Warning: this may explode!
        		pathInTerm.set(nextLevel, 0);
    			findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, curPosIsPositive, nextLevel, curPosIsPositive, qeps);
    		}
    	}else if(op== Quantifier.EX ){ 
    		if(curPosIsPositive){ //Quantifier that will be instantiated. Warning: this may explode!
        		pathInTerm.set(nextLevel, 0);
    			findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, curPosIsPositive, nextLevel, curPosIsPositive, qeps);
    		}else{ //Quantifier that will be Skolemized
    			//This is a potential query evaluation position. 
        		pathInTerm.set(nextLevel, 0);
    			findQueriesAndEvaluationPositions(t.sub(0), nextLevel, pathInTerm, curPosIsPositive, nextLevel, curPosIsPositive, qeps);
    		}
    	}else if(t.sort() == Sort.FORMULA){
    		Vector<Term> queries = collectQueries(t);
    		for(Term query:queries){
        		QueryEvalPos qep = new QueryEvalPos(query, (Vector<Integer>)pathInTerm.clone(), qepLevel+1, qepIsPositive);
        		qeps.add(qep);
        		System.out.println("AddedB: "+qep);
    		}
    	}
    	/*else if(op instanceof Junctor){
    		//Other Junctors like <-> must be handled explicitly. E.g. "<->" must be converted to "->" and "<-", so the query occurs in positive and negative position.
    		return;
    	}
    	*/
    }
    
    
    private Vector<Term> collectQueries(Term t){
    	Vector<Term> queries = new Vector<Term>();
    	collectQueriesRecursively(t,queries);
    	return queries;
    }
    
    
    /** Utility method called by <code>collectQueriesRecursively</code> */    
    private void collectQueriesRecursively(Term t, Vector<Term> result){
    	if(t.javaBlock()!=JavaBlock.EMPTY_JAVABLOCK){
    		System.out.println("collectQueriesRec encountered javaBlock.");
    		return;
    	}
    	if(t.op() instanceof ProgramMethod){ //Query found
    		System.out.println("Query found:"+t);
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
    private void removeRedundant(Vector<QueryEvalPos> qeps){
    	int size=qeps.size();
    	for(int i=0;i<size;i++){
    		QueryEvalPos cur = qeps.get(i);
    		for(int k=0;k<size;k++){
    			QueryEvalPos other = qeps.get(k);
    			if(i!=k && cur.subsumes(other)){
    				qeps.remove(k);
    				System.out.println("Removed:"+other);
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
    private class QueryEvalPos implements Comparable{
    	
    	/** The query that is subject to query evaluation/expansion. 
    	 * The query itself is not modified but a formula is added at a position 
    	 * described by the other fields. */
    	final public Term query;
    	/** Positive or negative position wrt. logical negation. 	 */
    	final public boolean positivePosition; 
    	/** Path in the syntax tree of the term where the query evaluation/expansion should be inserted. 
    	 *  The first element has no meaning and should be null. The path starts with the second element. */
    	final public Vector<Integer> pathInTerm;

    	public QueryEvalPos(Term query, Vector<Integer> path, int level, boolean isPositive){
    		this.query = query;
    		pathInTerm = (Vector<Integer>)path.clone();
			pathInTerm.setSize(level);
			positivePosition = isPositive;
    	}
    	
    	
    	public String toString(){
    		String pathstr = "[";
    		for(Integer in:pathInTerm){
    			pathstr += in+", ";
    		}
    		pathstr+="]";
    		return "QueryEvalPos of "+ (query!=null?query.toString():"NOQUERY")+ 
    				" in "+(positivePosition?"positive":"negative")+" position " +
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
    		if(!query.equals(other.query) || pathInTerm.size()>other.pathInTerm.size()){
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
		public int compareTo(Object arg0) {
			QueryEvalPos other = (QueryEvalPos)arg0;
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
        System.out.print(next+", ");
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
     */
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {		
        if (pio!=null && pio.subTerm().op() instanceof ProgramMethod && pio.subTerm().freeVars().isEmpty()) {
            final Term pmTerm = pio.subTerm();
            ProgramMethod pm = (ProgramMethod) pmTerm.op();
            final Sort nullSort = goal.proof().getJavaInfo().nullSort();
            if (pm.isStatic() || (pmTerm.sub(1).sort().extendsTrans(goal.proof().getJavaInfo().objectSort()) && 
                    !pmTerm.sub(1).sort().extendsTrans(nullSort))) {
                PIOPathIterator it = pio.iterator();
                while ( it.next() != -1 ) {
                    Term focus = it.getSubTerm();
                    if (focus.op() instanceof UpdateApplication || focus.op() instanceof Modality) {
                        return false;
                    }
                }
                return true;
            }
        }
        return false;
    }

}

