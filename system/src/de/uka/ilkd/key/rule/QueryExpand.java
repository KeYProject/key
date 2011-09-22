package de.uka.ilkd.key.rule;

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

    public static final BuiltInRule INSTANCE = new QueryExpand();

    private static Name QUERY_DEF_NAME = new Name("Evaluate Query");



    /**
     * Replaces in a term.
     */
    public Term replace(Term term, Term with, IntIterator it) {
        if ( !it.hasNext() ) {
            return with;
        }

        final int arity = term.arity();
        final Term newSubTerms[] = new Term[arity];    
        boolean changedSubTerm = false;
        int next = it.next();
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
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) {

        final PosInOccurrence pio = ruleApp.posInOccurrence();
        final Term query = pio.subTerm();

        final ProgramMethod method = (ProgramMethod)query.op();


        final ImmutableArray<ProgramVariable> args = getArgumentVariables(method.getParameters(), goal.node(), services);

        final ProgramVariable callee;
        final int offset;
        if (method.isStatic()) {
            callee = null;
            offset = 0;
        } else {
            callee = new LocationVariable(
                    new ProgramElementName(VariableNameProposer.DEFAULT.
                            getNameProposal("callee", services, goal.node())),
                            services.getJavaInfo().getKeYJavaType(query.sub(1).sort()));
            offset = 1;
        }

        final ProgramVariable result = 
                new LocationVariable(
                        new ProgramElementName(VariableNameProposer.DEFAULT.
                                getNameProposal("result", services, goal.node())), 
                                method.getKeYJavaType());


        final MethodReference mr = new MethodReference(args, method.getProgramElementName(), callee);
        final Function placeHolderResult = new Function(new Name(VariableNameProposer.DEFAULT.
                getNameProposal("res_"+method.getName(), services, goal.node())), query.sort());

        // construct method call   {heap:=h || p1:arg1 || ... || pn:=argn} 
        //                                  \[ res = o.m(p1,..,pn); \] (c = res) 

        final CopyAssignment assignment = new CopyAssignment(result, mr);
        final MethodFrame mf = new MethodFrame(null, 
                new ExecutionContext(new TypeRef(method.getContainerType()), null),
                new StatementBlock(assignment));
        final JavaBlock jb = JavaBlock.createJavaBlock(new StatementBlock(mf));	

        final TermBuilder tb = TermBuilder.DF;
        final Term methodCall = tb.box(jb, tb.equals(tb.func(placeHolderResult), tb.var(result)));


        Term update = tb.elementary(services, services.getTypeConverter().getHeapLDT().getHeap(), query.sub(0));
        if (callee != null) {
            update = tb.parallel(tb.elementary(services, tb.var(callee), query.sub(1)), update);
        }

        final Term[] argUpdates = new Term[args.size()]; 
        for (int i = 0; i<args.size(); i++) {
            argUpdates[i] = tb.elementary(services, tb.var(args.get(i)), query.sub(offset+1+i));
        }

        update = tb.parallel(update, tb.parallel(argUpdates));

        Term topLevel = tb.apply(update, methodCall);

        // new goal
        ImmutableList<Goal> newGoal = goal.split(1);
        Goal g = newGoal.head();

        // replace old query		
        g.addFormula(new SequentFormula(topLevel), true, true);	

        final Term newFormula = replace(pio.constrainedFormula().formula(), 
                tb.func(placeHolderResult), pio.posInTerm().iterator());
        g.changeFormula(new SequentFormula(newFormula), pio.topLevel());

        //register variables in namespace
        for (final ProgramVariable pv : args) { // add new program variables for arguments
            g.addProgramVariable(pv);
        }	
        if (callee != null) { g.addProgramVariable(callee); }
        g.addProgramVariable(result);
        services.getNamespaces().functions().add(placeHolderResult);

        return newGoal;
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
