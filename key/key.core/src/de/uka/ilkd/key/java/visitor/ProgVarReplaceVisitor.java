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

package de.uka.ilkd.key.java.visitor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.BlockSpecificationElement;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.speclang.MergeContract;
import de.uka.ilkd.key.speclang.PredicateAbstractionMergeContract;
import de.uka.ilkd.key.speclang.UnparameterizedMergeContract;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Walks through a java AST in depth-left-first-order. This visitor replaces a
 * number of program variables by others or new ones.
 */
public class ProgVarReplaceVisitor extends CreatingASTVisitor {

    // indicates if ALL program variables are to be replace by new
    // variables with the same name
    protected boolean replaceallbynew = true;

    /**
     * stores the program variables to be replaced as keys and the new program
     * variables as values
     */
    protected Map<ProgramVariable, ProgramVariable> replaceMap;

    private ProgramElement result = null;

    /**
     * creates a visitor that replaces the program variables in the given
     * statement by new ones with the same name
     *
     * @param st
     *            the statement where the prog vars are replaced
     * @param map
     *            the HashMap with the replacements
     * @param services
     *            the services instance
     */
    public ProgVarReplaceVisitor(ProgramElement st,
            Map<ProgramVariable, ProgramVariable> map, Services services) {
        super(st, true, services);
        this.replaceMap = map;
        assert services != null;
    }

    /**
     * creates a visitor that replaces the program variables in the given
     * statement
     *
     * @param st
     *            the statement where the prog vars are replaced
     * @param map
     *            the HashMap with the replacements
     * @param replaceall
     *            decides if all variables are to be replaced
     * @param services
     *            the services instance
     */
    public ProgVarReplaceVisitor(ProgramElement st,
            Map<ProgramVariable, ProgramVariable> map, boolean replaceall,
            Services services) {
        this(st, map, services);
        this.replaceallbynew = replaceall;
    }

    // %%% HACK: there should be a central facility for introducing new program
    // variables; this method is also used in <code>MethodCall</code> to
    // create copies of parameter variables
    public static LocationVariable copy(ProgramVariable pv) {
        return copy(pv, "");
    }

    // %%% HACK: there should be a central facility for introducing new program
    // variables; this method is also used in <code>MethodCall</code> to
    // create copies of parameter variables
    public static LocationVariable copy(ProgramVariable pv, String postFix) {
        ProgramElementName name = pv.getProgramElementName();
        // %%% HACK: final local variables are not renamed since they can occur
        // in an
        // anonymous class declared in their scope of visibility.
        /*
         * if(pv.isFinal()){ return pv; }
         */
        return new LocationVariable(
                VariableNamer.parseName(name.toString() + postFix,
                        name.getCreationInfo()),
                pv.getKeYJavaType(), pv.isFinal());
    }

    protected void walk(ProgramElement node) {
        if (node instanceof LocalVariableDeclaration && replaceallbynew) {
            LocalVariableDeclaration vd = (LocalVariableDeclaration) node;
            ImmutableArray<VariableSpecification> vspecs = vd
                    .getVariableSpecifications();
            for (int i = 0; i < vspecs.size(); i++) {
                ProgramVariable pv = (ProgramVariable) vspecs.get(i)
                        .getProgramVariable();
                if (!replaceMap.containsKey(pv)) {
                    replaceMap.put(pv, copy(pv));
                }
            }
        }
        super.walk(node);
    }

    /**
     * the action that is performed just before leaving the node the last time
     * @param node the node described above
     */
    protected void doAction(ProgramElement node) {
        node.visit(this);
    }

    /** starts the walker */
    public void start() {
        stack.push(new ExtList());
        walk(root());
        ExtList el = stack.peek();
        int i = 0;
        while (!(el.get(i) instanceof ProgramElement)) {
            i++;
        }
        result = (ProgramElement) stack.peek().get(i);
    }

    public ProgramElement result() {
        return result;
    }

    public void performActionOnProgramVariable(ProgramVariable pv) {
        ProgramElement newPV = replaceMap.get(pv);
        if (newPV != null) {
            addChild(newPV);
            changed();
        } else {
            doDefaultAction(pv);
        }
    }

    private Term replaceVariablesInTerm(Term t) {
        if (t == null) {
            return null;
        }
        if (t.op() instanceof ProgramVariable) {
            if (replaceMap.containsKey(t.op())) {
                ProgramVariable replacement = replaceMap.get(t.op());
                return services.getTermFactory().createTerm(replacement);
            } else {
                return t;
            }
        } else {
            boolean changed = false;
            Term subTerms[] = new Term[t.arity()];
            for (int i = 0, n = t.arity(); i < n; i++) {
                subTerms[i] = replaceVariablesInTerm(t.sub(i));
                changed = changed || subTerms[i] != t.sub(i);
            }
            Operator op = t.op();
            if (op instanceof ElementaryUpdate) {
                ElementaryUpdate uop = (ElementaryUpdate) t.op();
                if (replaceMap.containsKey(uop.lhs())) {
                    UpdateableOperator replacedLhs = (UpdateableOperator) replaceMap
                            .get(uop.lhs());
                    op = ElementaryUpdate.getInstance(replacedLhs);
                    changed = changed || uop != op;
                }
            }
            return changed ? services.getTermFactory().createTerm(op, subTerms,
                    t.boundVars(), t.javaBlock(), t.getLabels()) : t;
        }
    }

    private ImmutableList<Term> replaceVariablesInTerms(
            ImmutableList<Term> terms) {
        ImmutableList<Term> res = ImmutableSLList.<Term> nil();
        boolean changed = false;
        for (final Term term : terms) {
            final Term newTerm = replaceVariablesInTerm(term);
            changed |= newTerm != term;
            res = res.append(newTerm);
        }
        return changed ? res : terms;
    }

    private ImmutableList<InfFlowSpec> replaceVariablesInTermListTriples(
            ImmutableList<InfFlowSpec> terms) {
        ImmutableList<InfFlowSpec> res = ImmutableSLList.<InfFlowSpec> nil();
        boolean changed = false;
        for (final InfFlowSpec innerTerms : terms) {
            final ImmutableList<Term> renamedPreExpressions = replaceVariablesInTerms(
                    innerTerms.preExpressions);
            final ImmutableList<Term> renamedPostExpressions = replaceVariablesInTerms(
                    innerTerms.postExpressions);
            final ImmutableList<Term> renamedNewObjects = replaceVariablesInTerms(
                    innerTerms.newObjects);

            res = res.append(new InfFlowSpec(renamedPreExpressions,
                    renamedPostExpressions, renamedNewObjects));

            changed |= !(renamedPreExpressions == innerTerms.preExpressions
                    && renamedPostExpressions == innerTerms.postExpressions
                    && renamedNewObjects == innerTerms.newObjects);
        }
        return changed ? res : terms;
    }

    public void performActionOnLocationVariable(LocationVariable x) {
        performActionOnProgramVariable(x);
    }

    public void performActionOnProgramConstant(ProgramConstant x) {
        performActionOnProgramVariable(x);
    }

    @Override
    public void performActionOnBlockContract(final StatementBlock oldBlock,
            final StatementBlock newBlock) {
        ImmutableSet<BlockContract> oldContracts = services
                .getSpecificationRepository().getBlockContracts(oldBlock);
        for (BlockContract oldContract : oldContracts) {
            services.getSpecificationRepository()
                    .addBlockContract(createNewBlockContract(oldContract,
                            newBlock, !oldBlock.equals(newBlock)));
        }
    }

    @Override
    public void performActionOnLoopContract(final StatementBlock oldBlock,
            final StatementBlock newBlock) {
        ImmutableSet<LoopContract> oldContracts = services
                .getSpecificationRepository().getLoopContracts(oldBlock);
        for (LoopContract oldContract : oldContracts) {
            services.getSpecificationRepository()
                    .addLoopContract(createNewLoopContract(oldContract,
                            newBlock, !oldBlock.equals(newBlock)));
        }
    }

    @Override
    public void performActionOnMergeContract(MergeContract oldContract) {
        services.getSpecificationRepository()
                .removeMergeContracts(oldContract.getMergePointStatement());
        services.getSpecificationRepository()
                .addMergeContract(createNewMergeContract(oldContract,
                        oldContract.getMergePointStatement(), false));
    }

    @Override
    protected void performActionOnMergeContract(MergePointStatement oldMps,
            MergePointStatement newMps) {
        ImmutableSet<MergeContract> oldContracts = services
                .getSpecificationRepository().getMergeContracts(oldMps);
        services.getSpecificationRepository().removeMergeContracts(oldMps);
        oldContracts.forEach(c -> services.getSpecificationRepository()
                .addMergeContract(createNewMergeContract(c, newMps,
                        !oldMps.equals(newMps))));
    }

    private MergeContract createNewMergeContract(
            final MergeContract oldContract, final MergePointStatement newMps,
            final boolean changed) {

        if (oldContract instanceof UnparameterizedMergeContract && changed) {
            return new UnparameterizedMergeContract(
                    ((UnparameterizedMergeContract) oldContract)
                            .getInstantiatedMergeProcedure(services),
                    newMps, oldContract.getKJT());
        } else if (oldContract instanceof PredicateAbstractionMergeContract) {
            final PredicateAbstractionMergeContract pamc =
                    (PredicateAbstractionMergeContract) oldContract;
            final Map<LocationVariable, Term> atPres = pamc.getAtPres();

            final Map<LocationVariable, Term> saveCopy = new HashMap<LocationVariable, Term>(
                    atPres);
            for (Entry<LocationVariable, Term> h : saveCopy.entrySet()) {
                LocationVariable pv = h.getKey();
                final Term t = h.getValue();
                if (t == null) {
                    continue;
                }
                if (replaceMap.containsKey(pv)) {
                    atPres.remove(pv);
                    pv = (LocationVariable) replaceMap.get(pv);
                }
                atPres.put(pv, replaceVariablesInTerm(t));
            }

            return new PredicateAbstractionMergeContract(newMps, atPres,
                    pamc.getKJT(), pamc.getLatticeTypeName(),
                    pamc.getAbstractionPredicates(saveCopy, services).stream()
                            .map(pred -> AbstractionPredicate.create(
                                    replaceVariablesInTerm(
                                            pred.getPredicateFormWithPlaceholder().second),
                                    pred.getPredicateFormWithPlaceholder().first,
                                    services))
                            .collect(Collectors.toCollection(
                                () -> new ArrayList<AbstractionPredicate>())));

        } else {
            if (!changed) {
                return oldContract;
            }

            assert false : "ProgVarReplaceVisitor: Unknown type of MergeContract ("
                    + oldContract.getClass().getName() + ")";
        }

        // Nothing's changed
        return oldContract;
    }

    private BlockContract createNewBlockContract(
            final BlockContract oldContract, final StatementBlock newBlock,
            final boolean blockChanged) {
        final BlockContract.Variables newVariables = replaceBlockContractVariables(
                oldContract.getPlaceholderVariables());
        final Map<LocationVariable, Term> newPreconditions =
                new LinkedHashMap<LocationVariable, Term>();
        final Map<LocationVariable, Term> newPostconditions =
                new LinkedHashMap<LocationVariable, Term>();
        final Map<LocationVariable, Term> newModifiesClauses =
                new LinkedHashMap<LocationVariable, Term>();
        boolean changed = blockChanged;
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT()
                .getAllHeaps()) {
            final Term oldPrecondition = oldContract.getPrecondition(heap,
                    services);
            final Term oldPostcondition = oldContract.getPostcondition(heap,
                    services);
            final Term oldModifies = oldContract.getModifiesClause(heap,
                    services);

            final Term newPrecondition = replaceVariablesInTerm(
                    oldPrecondition);
            final Term newPostcondition = replaceVariablesInTerm(
                    oldPostcondition);
            final Term newModifies = replaceVariablesInTerm(oldModifies);

            newPreconditions.put(heap, (newPrecondition != oldPrecondition)
                    ? newPrecondition : oldPrecondition);
            newPostconditions.put(heap, (newPostcondition != oldPostcondition)
                    ? newPostcondition : oldPostcondition);
            newModifiesClauses.put(heap,
                    (newModifies != oldModifies) ? newModifies : oldModifies);

            changed |= ((newPrecondition != oldPrecondition)
                    || (newPostcondition != oldPostcondition)
                    || (newModifies != oldModifies));
        }
        final ImmutableList<InfFlowSpec> newInfFlowSpecs = replaceVariablesInTermListTriples(
                oldContract.getInfFlowSpecs());

        OpReplacer replacer = new OpReplacer(replaceMap, services.getTermFactory());

        return changed ? oldContract.update(newBlock, newPreconditions,
                newPostconditions, newModifiesClauses, newInfFlowSpecs,
                newVariables,
                replacer.replace(oldContract.getMby())) : oldContract;
    }

    private LoopContract createNewLoopContract(
            final LoopContract oldContract, final StatementBlock newBlock,
            final boolean blockChanged) {
        final LoopContract.Variables newVariables = replaceBlockContractVariables(
                oldContract.getPlaceholderVariables());
        final Map<LocationVariable, Term> newPreconditions =
                new LinkedHashMap<LocationVariable, Term>();
        final Map<LocationVariable, Term> newPostconditions =
                new LinkedHashMap<LocationVariable, Term>();
        final Map<LocationVariable, Term> newModifiesClauses =
                new LinkedHashMap<LocationVariable, Term>();
        boolean changed = blockChanged;
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT()
                .getAllHeaps()) {
            final Term oldPrecondition = oldContract.getPrecondition(heap,
                    services);
            final Term oldPostcondition = oldContract.getPostcondition(heap,
                    services);
            final Term oldModifies = oldContract.getModifiesClause(heap,
                    services);

            final Term newPrecondition = replaceVariablesInTerm(
                    oldPrecondition);
            final Term newPostcondition = replaceVariablesInTerm(
                    oldPostcondition);
            final Term newModifies = replaceVariablesInTerm(oldModifies);

            newPreconditions.put(heap, (newPrecondition != oldPrecondition)
                    ? newPrecondition : oldPrecondition);
            newPostconditions.put(heap, (newPostcondition != oldPostcondition)
                    ? newPostcondition : oldPostcondition);
            newModifiesClauses.put(heap,
                    (newModifies != oldModifies) ? newModifies : oldModifies);

            changed |= ((newPrecondition != oldPrecondition)
                    || (newPostcondition != oldPostcondition)
                    || (newModifies != oldModifies));
        }
        final ImmutableList<InfFlowSpec> newInfFlowSpecs = replaceVariablesInTermListTriples(
                oldContract.getInfFlowSpecs());

        OpReplacer replacer = new OpReplacer(replaceMap, services.getTermFactory());

        return changed ? oldContract.update(newBlock, newPreconditions,
                newPostconditions, newModifiesClauses, newInfFlowSpecs,
                newVariables,
                replacer.replace(oldContract.getMby()),
                replacer.replace(oldContract.getDecreases())) : oldContract;
    }

    private BlockSpecificationElement.Variables replaceBlockContractVariables(
            final BlockSpecificationElement.Variables variables) {
        return new BlockSpecificationElement.Variables(replaceVariable(variables.self),
                replaceFlags(variables.breakFlags),
                replaceFlags(variables.continueFlags),
                replaceVariable(variables.returnFlag),
                replaceVariable(variables.result),
                replaceVariable(variables.exception),
                replaceRemembranceHeaps(variables.remembranceHeaps),
                replaceRemembranceLocalVariables(
                        variables.remembranceLocalVariables),
                replaceRemembranceHeaps(variables.outerRemembranceHeaps),
                replaceRemembranceLocalVariables(
                        variables.outerRemembranceVariables),
                services);
    }

    private ProgramVariable replaceVariable(final ProgramVariable variable) {
        if (variable != null) {
            if (replaceMap.containsKey(variable)) {
                // TODO Can we really safely assume that replaceMap contains a
                // program variable?
                return replaceMap.get(variable);
            } else {
                if (replaceallbynew) {
                    replaceMap.put(variable, copy(variable));
                    return replaceMap.get(variable);
                } else {
                    return variable;
                }
            }
        } else {
            return null;
        }
    }

    private Map<Label, ProgramVariable> replaceFlags(
            final Map<Label, ProgramVariable> flags) {
        final Map<Label, ProgramVariable> result = new LinkedHashMap<Label, ProgramVariable>();
        for (Map.Entry<Label, ProgramVariable> flag : flags.entrySet()) {
            result.put(flag.getKey(), replaceVariable(flag.getValue()));
        }
        return result;
    }

    private Map<LocationVariable, LocationVariable> replaceRemembranceHeaps(
            final Map<LocationVariable, LocationVariable> remembranceHeaps) {
        final Map<LocationVariable, LocationVariable> result =
                new LinkedHashMap<LocationVariable, LocationVariable>();
        for (Map.Entry<LocationVariable, LocationVariable> remembranceHeap
                : remembranceHeaps.entrySet()) {
            // TODO Can we really safely assume that replaceVariable returns a
            // location variable?
            result.put(remembranceHeap.getKey(),
                    (LocationVariable) replaceVariable(
                            remembranceHeap.getValue()));
        }
        return result;
    }

    private Map<LocationVariable, LocationVariable> replaceRemembranceLocalVariables(
            final Map<LocationVariable, LocationVariable> remembranceLocalVariables) {
        final Map<LocationVariable, LocationVariable> result =
                new LinkedHashMap<LocationVariable, LocationVariable>();
        for (Map.Entry<LocationVariable, LocationVariable> remembranceLocalVariable
                : remembranceLocalVariables.entrySet()) {
            result.put(
                    (LocationVariable) replaceVariable(
                            remembranceLocalVariable.getKey()),
                    (LocationVariable) replaceVariable(
                            remembranceLocalVariable.getValue()));
        }
        return result;
    }

    public void performActionOnLoopInvariant(LoopStatement oldLoop,
            LoopStatement newLoop) {
        final TermBuilder tb = services.getTermBuilder();
        LoopSpecification inv = services.getSpecificationRepository()
                .getLoopSpec(oldLoop);
        if (inv == null) {
            return;
        }
        Term selfTerm = inv.getInternalSelfTerm();
        Map<LocationVariable, Term> atPres = inv.getInternalAtPres();

        Map<LocationVariable, Term> newInvariants =
                new LinkedHashMap<LocationVariable, Term>();
        Map<LocationVariable, Term> newFreeInvariants =
                new LinkedHashMap<LocationVariable, Term>();
        Map<LocationVariable, Term> newMods = new LinkedHashMap<LocationVariable, Term>();
        Map<LocationVariable, ImmutableList<InfFlowSpec>> newInfFlowSpecs =
                new LinkedHashMap<LocationVariable, ImmutableList<InfFlowSpec>>();

        for (LocationVariable heap : services.getTypeConverter().getHeapLDT()
                .getAllHeaps()) {
            final Term m = replaceVariablesInTerm(
                    inv.getModifies(heap, selfTerm, atPres, services));
            newMods.put(heap, m);
            final ImmutableList<InfFlowSpec> infFlowSpecs = replaceVariablesInTermListTriples(
                    inv.getInfFlowSpecs(heap, selfTerm, atPres, services));
            newInfFlowSpecs.put(heap, infFlowSpecs);

            final Term i = replaceVariablesInTerm(
                    inv.getInvariant(heap, selfTerm, atPres, services));
            newInvariants.put(heap, i);

            final Term j = replaceVariablesInTerm(
                    inv.getFreeInvariant(heap, selfTerm, atPres, services));
            newFreeInvariants.put(heap, j);

        }

        // variant
        Term newVariant = replaceVariablesInTerm(
                inv.getVariant(selfTerm, atPres, services));

        Term newSelfTerm = replaceVariablesInTerm(selfTerm);

        Map<LocationVariable, Term> saveCopy = new HashMap<LocationVariable, Term>(
                atPres);
        for (Entry<LocationVariable, Term> h : saveCopy.entrySet()) {
            LocationVariable pv = h.getKey();
            final Term t = h.getValue();
            if (t == null) {
                continue;
            }
            if (replaceMap.containsKey(pv)) {
                atPres.remove(pv);
                pv = (LocationVariable) replaceMap.get(pv);
            }
            atPres.put(pv, replaceVariablesInTerm(t));
        }

        ImmutableList<Term> newLocalIns = tb
                .var(MiscTools.getLocalIns(newLoop, services));
        ImmutableList<Term> newLocalOuts = tb
                .var(MiscTools.getLocalOuts(newLoop, services));

        LoopSpecification newInv = inv.create(newLoop, newInvariants,
                newFreeInvariants, newMods, newInfFlowSpecs, newVariant,
                newSelfTerm, newLocalIns, newLocalOuts, atPres);
        services.getSpecificationRepository().addLoopInvariant(newInv);
    }
}
