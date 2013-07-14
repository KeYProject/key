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

package de.uka.ilkd.key.java.visitor;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;
import de.uka.ilkd.key.util.ExtList;

/**
 * Walks through a java AST in depth-left-first-order. This visitor
 * replaces a number of program variables by others or new ones.
 */
public class ProgVarReplaceVisitor extends CreatingASTVisitor {

    private ProgramElement result=null;

    // indicates if ALL program variables are to be replace by new
    // variables with the same name
    protected boolean replaceallbynew=true;


    /**
     * stores the program variables to be replaced as keys and the new
     * program variables as values
     */
    protected Map<ProgramVariable, ProgramVariable> replaceMap;


    /**
     * creates a visitor that replaces the program variables in the given
     * statement by new ones with the same name
     * @param st the statement where the prog vars are replaced
     * @param map the HashMap with the replacements
     */
    public ProgVarReplaceVisitor(ProgramElement st, Map<ProgramVariable, ProgramVariable> map, Services services) {
    super(st, true, services);
    this.replaceMap = map;
        assert services != null;
    }


    /**
     * creates a visitor that replaces the program variables in the given
     * statement
     * @param st the statement where the prog vars are replaced
     * @param map the HashMap with the replacements
     * @param replaceall decides if all variables are to be replaced
     */
    public ProgVarReplaceVisitor(ProgramElement st,
                                 Map<ProgramVariable, ProgramVariable> map,
                                 boolean replaceall,
                                 Services services) {
        this(st, map, services);
        this.replaceallbynew = replaceall;
    }


    //%%% HACK: there should be a central facility for introducing new program
    // variables; this method is also used in <code>MethodCall</code> to
    // create copies of parameter variables
    public static LocationVariable copy(ProgramVariable pv) {
    return copy(pv, "");
    }


    //%%% HACK: there should be a central facility for introducing new program
    // variables; this method is also used in <code>MethodCall</code> to
    // create copies of parameter variables
    public static LocationVariable copy(ProgramVariable pv, String postFix) {
        ProgramElementName name = pv.getProgramElementName();
        //%%% HACK: final local variables are not renamed since they can occur in an
        // anonymous class declared in their scope of visibility.
/*      if(pv.isFinal()){
            return pv;
        }*/
    return new LocationVariable
        (VariableNamer.parseName(name.toString() + postFix,
                         name.getCreationInfo()),
         pv.getKeYJavaType(), pv.isFinal());
    }


    protected void walk(ProgramElement node) {
    if (node instanceof LocalVariableDeclaration && replaceallbynew) {
        LocalVariableDeclaration vd= (LocalVariableDeclaration)node;
        ImmutableArray<VariableSpecification> vspecs=vd.getVariableSpecifications();
        for (int i=0; i<vspecs.size(); i++) {
        ProgramVariable pv
            = (ProgramVariable)
                 vspecs.get(i).getProgramVariable();
        if (!replaceMap.containsKey(pv)) {
            replaceMap.put(pv, copy(pv));
        }
        }
    }
    super.walk(node);
    }


    /** the action that is performed just before leaving the node the
     * last time
     */
    protected void doAction(ProgramElement node) {
    node.visit(this);
    }


    /** starts the walker*/
    public void start() {
    stack.push(new ExtList());
    walk(root());
    ExtList el= stack.peek();
    int i=0;
    while (!(el.get(i) instanceof ProgramElement)) {
        i++;
    }
    result=(ProgramElement) stack.peek().get(i);
    }


    public ProgramElement result() {
    return result;
    }


    public void performActionOnProgramVariable(ProgramVariable pv) {
    ProgramElement newPV = (ProgramElement) replaceMap.get(pv);
    if (newPV!=null) {
        addChild(newPV);
        changed();
    } else {
        doDefaultAction(pv);
    }
    }

    private Term replaceVariablesInTerm(Term t){
        if(t==null) {
            return null;
        }
    if(t.op() instanceof ProgramVariable) {
        if(replaceMap.containsKey(t.op())) {
            ProgramVariable replacement = replaceMap.get(t.op());
            return TermFactory.DEFAULT.createTerm(replacement);
        } else {
            return t;
        }
    } else {
        Term subTerms[] = new Term[t.arity()];
        for(int i = 0, n = t.arity(); i < n; i++) {
        subTerms[i] = replaceVariablesInTerm(t.sub(i));
        }
        Operator op = t.op();
        if(op instanceof ElementaryUpdate) {
        ElementaryUpdate uop = (ElementaryUpdate) t.op();
        if(replaceMap.containsKey(uop.lhs())) {
            UpdateableOperator replacedLhs
                = (UpdateableOperator) replaceMap.get(uop.lhs());
            op = ElementaryUpdate.getInstance(replacedLhs);
        }
        }
        return TermFactory.DEFAULT.createTerm(op,
                              subTerms,
                              t.boundVars(),
                              t.javaBlock());
    }
    }

    private ImmutableSet<Term> replaceVariablesInTerms(ImmutableSet<Term> terms) {
        ImmutableSet<Term> res = DefaultImmutableSet.nil();
        for (final Term term : terms) {
            res = res.add(replaceVariablesInTerm(term));
        }
        return res;
    }


    public void performActionOnLocationVariable(LocationVariable x) {
       performActionOnProgramVariable(x);
    }


    public void performActionOnProgramConstant(ProgramConstant x) {
        performActionOnProgramVariable(x);
    }

    public void performActionOnBlockContract(final StatementBlock oldBlock, final StatementBlock newBlock) {
        ImmutableSet<BlockContract> oldContracts = services.getSpecificationRepository().getBlockContracts(oldBlock);
        for (BlockContract oldContract : oldContracts) {
            services.getSpecificationRepository().addBlockContract(createNewBlockContract(oldContract, newBlock));
        }
    }

    private BlockContract createNewBlockContract(final BlockContract oldContract, final StatementBlock newBlock)
    {
       final BlockContract.Variables newVariables = replaceBlockContractVariables(oldContract.getPlaceholderVariables());
        final Map<LocationVariable, Term> newPreconditions = new LinkedHashMap<LocationVariable, Term>();
        final Map<LocationVariable, Term> newPostconditions = new LinkedHashMap<LocationVariable, Term>();
        final Map<LocationVariable, Term> newModifiesClauses = new LinkedHashMap<LocationVariable, Term>();
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            newPreconditions.put(heap, replaceVariablesInTerm(oldContract.getPrecondition(heap, services)));
            newPostconditions.put(heap, replaceVariablesInTerm(oldContract.getPostcondition(heap, services)));
            newModifiesClauses.put(heap, replaceVariablesInTerm(oldContract.getModifiesClause(heap, services)));
        }
        return oldContract.update(newBlock, newPreconditions, newPostconditions, newModifiesClauses, newVariables);
    }

    private BlockContract.Variables replaceBlockContractVariables(final BlockContract.Variables variables)
    {
        return new BlockContract.Variables(
            replaceVariable(variables.self),
            replaceFlags(variables.breakFlags),
            replaceFlags(variables.continueFlags),
            replaceVariable(variables.returnFlag),
            replaceVariable(variables.result),
            replaceVariable(variables.exception),
            replaceRemembranceHeaps(variables.remembranceHeaps),
            replaceRemembranceLocalVariables(variables.remembranceLocalVariables)
        );
    }

    private ProgramVariable replaceVariable(final ProgramVariable variable)
    {
        if (variable != null) {
            if (replaceMap.containsKey(variable)) {
                // TODO Can we really safely assume that replaceMap contains a program variable?
                return (ProgramVariable) replaceMap.get(variable);
            }
            else {
                if (replaceallbynew) {
                    replaceMap.put(variable, copy(variable));
                    return (ProgramVariable) replaceMap.get(variable);
                }
                else {
                    return variable;
                }
            }
        }
        else {
            return null;
        }
    }

    private Map<Label, ProgramVariable> replaceFlags(final Map<Label, ProgramVariable> flags)
    {
        final Map<Label, ProgramVariable> result = new LinkedHashMap<Label, ProgramVariable>();
        for (Map.Entry<Label, ProgramVariable> flag : flags.entrySet()) {
            result.put(flag.getKey(), replaceVariable(flag.getValue()));
        }
        return result;
    }

    private Map<LocationVariable, LocationVariable> replaceRemembranceHeaps(final Map<LocationVariable, LocationVariable> remembranceHeaps) {
        final Map<LocationVariable, LocationVariable> result = new LinkedHashMap<LocationVariable, LocationVariable>();
        for (Map.Entry<LocationVariable, LocationVariable> remembranceHeap: remembranceHeaps.entrySet()) {
            // TODO Can we really safely assume that replaceVariable returns a location variable?
            result.put(
                remembranceHeap.getKey(),
                (LocationVariable) replaceVariable(remembranceHeap.getValue())
            );
        }
        return result;
    }

    private Map<LocationVariable, LocationVariable> replaceRemembranceLocalVariables(final Map<LocationVariable, LocationVariable> remembranceLocalVariables) {
        final Map<LocationVariable, LocationVariable> result = new LinkedHashMap<LocationVariable, LocationVariable>();
        for (Map.Entry<LocationVariable, LocationVariable> remembranceLocalVariable: remembranceLocalVariables.entrySet()) {
            result.put(
                (LocationVariable) replaceVariable(remembranceLocalVariable.getKey()),
                (LocationVariable) replaceVariable(remembranceLocalVariable.getValue())
            );
        }
        return result;
    }

    public void performActionOnLoopInvariant(LoopStatement oldLoop,
                                             LoopStatement newLoop) {
        LoopInvariant inv
            = services.getSpecificationRepository().getLoopInvariant(oldLoop);
        if(inv == null) {
            return;
        }
        Term selfTerm = inv.getInternalSelfTerm();
        Map<LocationVariable,Term> atPres = inv.getInternalAtPres();

        Map<LocationVariable,Term> newInvariants = new LinkedHashMap<LocationVariable,Term>();
        Map<LocationVariable,Term> newMods = new LinkedHashMap<LocationVariable,Term>();

        for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
           final Term m = replaceVariablesInTerm(inv.getModifies(heap, selfTerm,
                                     atPres,
                                     services));
           newMods.put(heap, m);
           final Term i = replaceVariablesInTerm(inv.getInvariant(heap, selfTerm,
                                     atPres,
                                     services));
           newInvariants.put(heap, i);
        }

        //variant
        Term newVariant
            = replaceVariablesInTerm(inv.getVariant(selfTerm,
                                                    atPres,
                                                    services));

        Term newSelfTerm = replaceVariablesInTerm(selfTerm);

        for(Entry<LocationVariable, Term> h : atPres.entrySet()) {
           final Term t = h.getValue();
           if(t == null) continue;
           atPres.put(h.getKey(), replaceVariablesInTerm(t));
        }

        LoopInvariant newInv
            = new LoopInvariantImpl(newLoop,
                                    newInvariants,
                                    newMods,
                                    newVariant,
                                    newSelfTerm,
                                    atPres);
        services.getSpecificationRepository().addLoopInvariant(newInv);
    }
}
