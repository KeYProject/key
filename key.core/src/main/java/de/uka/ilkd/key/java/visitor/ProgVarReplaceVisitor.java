/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import java.util.*;
import java.util.Map.Entry;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.op.Operator;
import org.key_project.logic.op.UpdateableOperator;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 * Walks through a java AST in depth-left-first-order. This visitor replaces a number of program
 * variables by others or new ones.
 */
public class ProgVarReplaceVisitor extends CreatingASTVisitor {

    // indicates if ALL program variables are to be replace by new
    // variables with the same name
    protected boolean replaceallbynew = true;

    /**
     * stores the program variables to be replaced as keys and the new program variables as values
     */
    protected final Map<LocationVariable, LocationVariable> replaceMap;

    private ProgramElement result = null;

    /**
     * creates a visitor that replaces the program variables in the given statement by new ones with
     * the same name
     *
     * @param st the statement where the prog vars are replaced
     * @param map the HashMap with the replacements
     * @param services the services instance
     */
    public ProgVarReplaceVisitor(ProgramElement st, Map<LocationVariable, LocationVariable> map,
            Services services) {
        super(st, true, services);
        this.replaceMap = map;
        assert services != null;
    }

    /**
     * creates a visitor that replaces the program variables in the given statement
     *
     * @param st the statement where the prog vars are replaced
     * @param map the HashMap with the replacements
     * @param replaceall decides if all variables are to be replaced
     * @param services the services instance
     */
    public ProgVarReplaceVisitor(ProgramElement st, Map<LocationVariable, LocationVariable> map,
            boolean replaceall, Services services) {
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
        return LocationVariable.fromProgramVariable(pv,
            VariableNamer.parseName(name.toString() + postFix, name.getCreationInfo()));
    }

    @Override
    protected void walk(ProgramElement node) {
        if (node instanceof LocalVariableDeclaration vd && replaceallbynew) {
            ImmutableArray<VariableSpecification> vspecs = vd.getVariableSpecifications();
            for (int i = 0; i < vspecs.size(); i++) {
                var pv = (LocationVariable) vspecs.get(i).getProgramVariable();
                if (!replaceMap.containsKey(pv)) {
                    replaceMap.put(pv, copy(pv));
                }
            }
        }
        super.walk(node);
    }

    /**
     * the action that is performed just before leaving the node the last time
     *
     * @param node the node described above
     */
    @Override
    protected void doAction(ProgramElement node) {
        node.visit(this);
    }

    /** starts the walker */
    @Override
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

    @Override
    public void performActionOnProgramVariable(ProgramVariable pv) {
        ProgramElement newPV = replaceMap.get(pv);
        if (newPV != null) {
            addChild(newPV);
            changed();
        } else {
            doDefaultAction(pv);
        }
    }

    private JTerm replaceVariablesInTerm(JTerm t) {
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
            JTerm[] subTerms = new JTerm[t.arity()];
            for (int i = 0, n = t.arity(); i < n; i++) {
                subTerms[i] = replaceVariablesInTerm(t.sub(i));
                changed = changed || subTerms[i] != t.sub(i);
            }
            Operator op = t.op();
            if (op instanceof ElementaryUpdate) {
                ElementaryUpdate uop = (ElementaryUpdate) t.op();
                if (replaceMap.containsKey(uop.lhs())) {
                    UpdateableOperator replacedLhs = replaceMap.get(uop.lhs());
                    op = ElementaryUpdate.getInstance(replacedLhs);
                    changed = changed || uop != op;
                }
            }
            return changed ? services.getTermFactory().createTerm(op, subTerms, t.boundVars(),
                t.getLabels()) : t;
        }
    }

    private ImmutableList<JTerm> replaceVariablesInTerms(ImmutableList<JTerm> terms) {
        ImmutableList<JTerm> res = ImmutableSLList.nil();
        boolean changed = false;
        for (final JTerm term : terms) {
            final JTerm newTerm = replaceVariablesInTerm(term);
            changed |= newTerm != term;
            res = res.append(newTerm);
        }
        return changed ? res : terms;
    }

    private ImmutableList<InfFlowSpec> replaceVariablesInTermListTriples(
            ImmutableList<InfFlowSpec> terms) {
        ImmutableList<InfFlowSpec> res = ImmutableSLList.nil();
        boolean changed = false;
        for (final InfFlowSpec innerTerms : terms) {
            final ImmutableList<JTerm> renamedPreExpressions =
                replaceVariablesInTerms(innerTerms.preExpressions);
            final ImmutableList<JTerm> renamedPostExpressions =
                replaceVariablesInTerms(innerTerms.postExpressions);
            final ImmutableList<JTerm> renamedNewObjects =
                replaceVariablesInTerms(innerTerms.newObjects);

            res = res.append(
                new InfFlowSpec(renamedPreExpressions, renamedPostExpressions, renamedNewObjects));

            changed |= !(renamedPreExpressions == innerTerms.preExpressions
                    && renamedPostExpressions == innerTerms.postExpressions
                    && renamedNewObjects == innerTerms.newObjects);
        }
        return changed ? res : terms;
    }

    @Override
    public void performActionOnLocationVariable(LocationVariable x) {
        performActionOnProgramVariable(x);
    }

    @Override
    public void performActionOnProgramConstant(ProgramConstant x) {
        performActionOnProgramVariable(x);
    }

    @Override
    public void performActionOnBlockContract(final StatementBlock oldBlock,
            final StatementBlock newBlock) {
        ImmutableSet<BlockContract> oldContracts =
            services.getSpecificationRepository().getBlockContracts(oldBlock);
        for (BlockContract oldContract : oldContracts) {
            BlockContract newContract =
                createNewBlockContract(oldContract, newBlock, !oldBlock.equals(newBlock));

            if (newContract != oldContract) {
                if (oldBlock.equals(newBlock)) {
                    services.getSpecificationRepository().removeBlockContract(oldContract);
                }
                services.getSpecificationRepository().addBlockContract(newContract);
            }
        }
    }

    @Override
    public void performActionOnLoopContract(final StatementBlock oldBlock,
            final StatementBlock newBlock) {
        ImmutableSet<LoopContract> oldContracts =
            services.getSpecificationRepository().getLoopContracts(oldBlock);
        for (LoopContract oldContract : oldContracts) {
            LoopContract newContract =
                createNewLoopContract(oldContract, newBlock, !oldBlock.equals(newBlock));

            if (newContract != oldContract) {
                if (oldBlock.equals(newBlock)) {
                    services.getSpecificationRepository().removeLoopContract(oldContract);
                }
                services.getSpecificationRepository().addLoopContract(newContract);
            }
        }
    }

    @Override
    public void performActionOnLoopContract(final LoopStatement oldLoop,
            final LoopStatement newLoop) {
        ImmutableSet<LoopContract> oldContracts =
            services.getSpecificationRepository().getLoopContracts(oldLoop);
        for (LoopContract oldContract : oldContracts) {
            services.getSpecificationRepository().addLoopContract(
                createNewLoopContract(oldContract, newLoop, !oldLoop.equals(newLoop)));
        }
    }

    @Override
    public void performActionOnMergeContract(MergeContract oldContract) {
        services.getSpecificationRepository()
                .removeMergeContracts(oldContract.getMergePointStatement());
        services.getSpecificationRepository().addMergeContract(
            createNewMergeContract(oldContract, oldContract.getMergePointStatement(), false));
    }

    @Override
    protected void performActionOnMergeContract(MergePointStatement oldMps,
            MergePointStatement newMps) {
        ImmutableSet<MergeContract> oldContracts =
            services.getSpecificationRepository().getMergeContracts(oldMps);
        services.getSpecificationRepository().removeMergeContracts(oldMps);
        oldContracts.forEach(c -> services.getSpecificationRepository()
                .addMergeContract(createNewMergeContract(c, newMps, !oldMps.equals(newMps))));
    }

    private MergeContract createNewMergeContract(final MergeContract oldContract,
            final MergePointStatement newMps, final boolean changed) {

        if (oldContract instanceof UnparameterizedMergeContract && changed) {
            return new UnparameterizedMergeContract(
                oldContract.getInstantiatedMergeProcedure(services), newMps, oldContract.getKJT());
        } else if (oldContract instanceof PredicateAbstractionMergeContract pamc) {
            final Map<LocationVariable, JTerm> atPres = pamc.getAtPres();

            final Map<LocationVariable, JTerm> saveCopy =
                new HashMap<>(atPres);
            for (Entry<LocationVariable, JTerm> h : saveCopy.entrySet()) {
                LocationVariable pv = h.getKey();
                final JTerm t = h.getValue();
                if (t == null) {
                    continue;
                }
                if (replaceMap.containsKey(pv)) {
                    atPres.remove(pv);
                    pv = replaceMap.get(pv);
                }
                atPres.put(pv, replaceVariablesInTerm(t));
            }

            return new PredicateAbstractionMergeContract(newMps, atPres, pamc.getKJT(),
                pamc.getLatticeTypeName(),
                pamc.getAbstractionPredicates(saveCopy, services).stream()
                        .map(pred -> AbstractionPredicate.create(
                            replaceVariablesInTerm(pred.getPredicateFormWithPlaceholder().second),
                            pred.getPredicateFormWithPlaceholder().first, services))
                        .collect(
                            Collectors.toCollection(ArrayList::new)));

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

    private BlockContract createNewBlockContract(final BlockContract oldContract,
            final StatementBlock newBlock, final boolean blockChanged) {
        final BlockContract.Variables newVariables =
            replaceBlockContractVariables(oldContract.getPlaceholderVariables());
        final Map<LocationVariable, JTerm> newPreconditions =
            new LinkedHashMap<>();
        final Map<LocationVariable, JTerm> newFreePreconditions =
            new LinkedHashMap<>();
        final Map<LocationVariable, JTerm> newPostconditions =
            new LinkedHashMap<>();
        final Map<LocationVariable, JTerm> newFreePostconditions =
            new LinkedHashMap<>();
        final Map<LocationVariable, JTerm> newModifiableClauses =
            new LinkedHashMap<>();
        final Map<LocationVariable, JTerm> newFreeModifiableClauses =
            new LinkedHashMap<LocationVariable, JTerm>();
        boolean changed = blockChanged;

        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            final JTerm oldPrecondition = oldContract.getPrecondition(heap, services);
            final JTerm oldFreePrecondition = oldContract.getFreePrecondition(heap, services);
            final JTerm oldPostcondition = oldContract.getPostcondition(heap, services);
            final JTerm oldFreePostcondition = oldContract.getFreePostcondition(heap, services);
            final JTerm oldModifiable = oldContract.getModifiableClause(heap, services);
            final JTerm oldFreeModifiable = oldContract.getFreeModifiableClause(heap, services);

            final JTerm newPrecondition = replaceVariablesInTerm(oldPrecondition);
            final JTerm newFreePrecondition = replaceVariablesInTerm(oldFreePrecondition);
            final JTerm newPostcondition = replaceVariablesInTerm(oldPostcondition);
            final JTerm newFreePostcondition = replaceVariablesInTerm(oldFreePostcondition);
            final JTerm newModifiable = replaceVariablesInTerm(oldModifiable);
            final JTerm newFreeModifiable = replaceVariablesInTerm(oldFreeModifiable);

            newPreconditions.put(heap, newPrecondition);
            newFreePreconditions.put(heap, newFreePrecondition);
            newPostconditions.put(heap, newPostcondition);
            newFreePostconditions.put(heap, newFreePostcondition);
            newModifiableClauses.put(heap, newModifiable);
            newFreeModifiableClauses.put(heap, newFreeModifiable);

            changed |= ((newPrecondition != oldPrecondition)
                    || (newFreePrecondition != oldFreePrecondition)
                    || (newPostcondition != oldPostcondition)
                    || (newFreePostcondition != oldFreePostcondition)
                    || (newModifiable != oldModifiable)
                    || (newFreeModifiable != oldFreeModifiable));
        }
        final ImmutableList<InfFlowSpec> newInfFlowSpecs =
            replaceVariablesInTermListTriples(oldContract.getInfFlowSpecs());

        OpReplacer replacer =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());

        return changed
                ? oldContract.update(newBlock, newPreconditions, newFreePreconditions,
                    newPostconditions, newFreePostconditions, newModifiableClauses,
                    newFreeModifiableClauses, newInfFlowSpecs, newVariables,
                    replacer.replace(oldContract.getMby()))
                : oldContract;
    }

    private LoopContract createNewLoopContract(final LoopContract oldContract,
            final JavaStatement newStatement, final boolean blockChanged) {
        final LoopContract.Variables newVariables =
            replaceBlockContractVariables(oldContract.getPlaceholderVariables());
        final Map<LocationVariable, JTerm> newPreconditions = new LinkedHashMap<>();
        final Map<LocationVariable, JTerm> newFreePreconditions = new LinkedHashMap<>();
        final Map<LocationVariable, JTerm> newPostconditions = new LinkedHashMap<>();
        final Map<LocationVariable, JTerm> newFreePostconditions = new LinkedHashMap<>();
        final Map<LocationVariable, JTerm> newModifiableClauses = new LinkedHashMap<>();
        final Map<LocationVariable, JTerm> newFreeModifiableClauses = new LinkedHashMap<>();
        boolean changed = blockChanged;

        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            final JTerm oldPrecondition = oldContract.getPrecondition(heap, services);
            final JTerm oldFreePrecondition = oldContract.getFreePrecondition(heap, services);
            final JTerm oldPostcondition = oldContract.getPostcondition(heap, services);
            final JTerm oldFreePostcondition = oldContract.getFreePostcondition(heap, services);
            final JTerm oldModifiable = oldContract.getModifiableClause(heap, services);
            final JTerm oldFreeModifiable = oldContract.getFreeModifiableClause(heap, services);

            final JTerm newPrecondition = replaceVariablesInTerm(oldPrecondition);
            final JTerm newFreePrecondition = replaceVariablesInTerm(oldFreePrecondition);
            final JTerm newPostcondition = replaceVariablesInTerm(oldPostcondition);
            final JTerm newFreePostcondition = replaceVariablesInTerm(oldFreePostcondition);
            final JTerm newModifiable = replaceVariablesInTerm(oldModifiable);
            final JTerm newFreeModifiable = replaceVariablesInTerm(oldFreeModifiable);

            newPreconditions.put(heap, newPrecondition);
            newFreePreconditions.put(heap, newFreePrecondition);
            newPostconditions.put(heap, newPostcondition);
            newFreePostconditions.put(heap, newFreePostcondition);
            newModifiableClauses.put(heap, newModifiable);
            newFreeModifiableClauses.put(heap, newFreeModifiable);

            changed |= ((newPrecondition != oldPrecondition)
                    || (newFreePrecondition != oldFreePrecondition)
                    || (newPostcondition != oldPostcondition)
                    || (newFreePostcondition != oldFreePostcondition)
                    || (newModifiable != oldModifiable)
                    || (newFreeModifiable != oldFreeModifiable));
        }
        final ImmutableList<InfFlowSpec> newInfFlowSpecs =
            replaceVariablesInTermListTriples(oldContract.getInfFlowSpecs());

        OpReplacer replacer =
            new OpReplacer(replaceMap, services.getTermFactory(), services.getProof());

        if (!changed) {
            return oldContract;
        } else if (newStatement instanceof StatementBlock) {
            return oldContract.update((StatementBlock) newStatement, newPreconditions,
                newFreePreconditions, newPostconditions, newFreePostconditions,
                newModifiableClauses,
                newFreeModifiableClauses, newInfFlowSpecs, newVariables,
                replacer.replace(oldContract.getMby()),
                replacer.replace(oldContract.getDecreases()));
        } else {
            return oldContract.update((LoopStatement) newStatement, newPreconditions,
                newFreePreconditions, newPostconditions, newFreePostconditions,
                newModifiableClauses,
                newFreeModifiableClauses, newInfFlowSpecs, newVariables,
                replacer.replace(oldContract.getMby()),
                replacer.replace(oldContract.getDecreases()));
        }
    }

    private AuxiliaryContract.Variables replaceBlockContractVariables(
            final AuxiliaryContract.Variables variables) {
        return new AuxiliaryContract.Variables(replaceVariable(variables.self),
            replaceFlags(variables.breakFlags), replaceFlags(variables.continueFlags),
            replaceVariable(variables.returnFlag), replaceVariable(variables.result),
            replaceVariable(variables.exception),
            replaceRemembranceHeaps(variables.remembranceHeaps),
            replaceRemembranceLocalVariables(variables.remembranceLocalVariables),
            replaceRemembranceHeaps(variables.outerRemembranceHeaps),
            replaceRemembranceLocalVariables(variables.outerRemembranceVariables), services);
    }

    private LocationVariable replaceVariable(final LocationVariable variable) {
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

    private Map<Label, LocationVariable> replaceFlags(final Map<Label, LocationVariable> flags) {
        final Map<Label, LocationVariable> result = new LinkedHashMap<>();
        for (Map.Entry<Label, LocationVariable> flag : flags.entrySet()) {
            result.put(flag.getKey(), replaceVariable(flag.getValue()));
        }
        return result;
    }

    private Map<LocationVariable, LocationVariable> replaceRemembranceHeaps(
            final Map<LocationVariable, LocationVariable> remembranceHeaps) {
        final Map<LocationVariable, LocationVariable> result =
            new LinkedHashMap<>();
        for (Map.Entry<LocationVariable, LocationVariable> remembranceHeap : remembranceHeaps
                .entrySet()) {
            // TODO Can we really safely assume that replaceVariable returns a
            // location variable?
            result.put(remembranceHeap.getKey(),
                replaceVariable(remembranceHeap.getValue()));
        }
        return result;
    }

    private Map<LocationVariable, LocationVariable> replaceRemembranceLocalVariables(
            final Map<LocationVariable, LocationVariable> remembranceLocalVariables) {
        final Map<LocationVariable, LocationVariable> result =
            new LinkedHashMap<>();
        for (Map.Entry<LocationVariable, LocationVariable> remembranceLocalVariable : remembranceLocalVariables
                .entrySet()) {
            result.put(replaceVariable(remembranceLocalVariable.getKey()),
                replaceVariable(remembranceLocalVariable.getValue()));
        }
        return result;
    }

    @Override
    public void performActionOnLoopInvariant(LoopStatement oldLoop, LoopStatement newLoop) {
        final TermBuilder tb = services.getTermBuilder();
        LoopSpecification inv = services.getSpecificationRepository().getLoopSpec(oldLoop);
        if (inv == null) {
            return;
        }
        JTerm selfTerm = inv.getInternalSelfTerm();
        Map<LocationVariable, JTerm> atPres = inv.getInternalAtPres();

        Map<LocationVariable, JTerm> newInvariants = new LinkedHashMap<>();
        Map<LocationVariable, JTerm> newFreeInvariants = new LinkedHashMap<>();
        Map<LocationVariable, JTerm> newMods = new LinkedHashMap<>();
        Map<LocationVariable, JTerm> newFreeMods = new LinkedHashMap<LocationVariable, JTerm>();
        Map<LocationVariable, ImmutableList<InfFlowSpec>> newInfFlowSpecs =
            new LinkedHashMap<>();

        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            final JTerm m =
                replaceVariablesInTerm(inv.getModifiable(heap, selfTerm, atPres, services));
            newMods.put(heap, m);

            final JTerm mf = replaceVariablesInTerm(
                inv.getFreeModifiable(heap, selfTerm, atPres, services));
            newFreeMods.put(heap, mf);

            final ImmutableList<InfFlowSpec> infFlowSpecs = replaceVariablesInTermListTriples(
                inv.getInfFlowSpecs(heap, selfTerm, atPres, services));
            newInfFlowSpecs.put(heap, infFlowSpecs);

            final JTerm i =
                replaceVariablesInTerm(inv.getInvariant(heap, selfTerm, atPres, services));
            newInvariants.put(heap, i);

            final JTerm j =
                replaceVariablesInTerm(inv.getFreeInvariant(heap, selfTerm, atPres, services));
            newFreeInvariants.put(heap, j);

        }

        // variant
        JTerm newVariant = replaceVariablesInTerm(inv.getVariant(selfTerm, atPres, services));

        JTerm newSelfTerm = replaceVariablesInTerm(selfTerm);

        Map<LocationVariable, JTerm> saveCopy = new HashMap<>(atPres);
        for (Entry<LocationVariable, JTerm> h : saveCopy.entrySet()) {
            LocationVariable pv = h.getKey();
            final JTerm t = h.getValue();
            if (t == null) {
                continue;
            }
            if (replaceMap.containsKey(pv)) {
                atPres.remove(pv);
                pv = replaceMap.get(pv);
            }
            atPres.put(pv, replaceVariablesInTerm(t));
        }

        ImmutableList<JTerm> newLocalIns = tb.var(MiscTools.getLocalIns(newLoop, services));
        ImmutableList<JTerm> newLocalOuts = tb.var(MiscTools.getLocalOuts(newLoop, services));

        LoopSpecification newInv = inv.create(newLoop, newInvariants, newFreeInvariants, newMods,
            newFreeMods, newInfFlowSpecs, newVariant, newSelfTerm, newLocalIns, newLocalOuts,
            atPres);
        services.getSpecificationRepository().addLoopInvariant(newInv);
    }

    @Override
    public void performActionOnJmlAssert(final JmlAssert x) {
        handleJmlStatements(x, JmlAssert::new);
    }

    @Override
    public void performActionOnSetStatement(final SetStatement x) {
        /*
         * var spec =
         * Objects.requireNonNull(services.getSpecificationRepository().getStatementSpec(x));
         * ProgramVariableCollection vars = spec.vars();
         * Map<LocationVariable, Term> atPres = vars.atPres;
         * Map<LocationVariable, Term> newAtPres = new LinkedHashMap<>(atPres);
         * Map<LocationVariable, LocationVariable> atPreVars = vars.atPreVars;
         * Map<LocationVariable, LocationVariable> newAtPreVars = new LinkedHashMap<>(atPreVars);
         *
         * for (Entry<LocationVariable, Term> e : atPres.entrySet()) {
         * LocationVariable pv = e.getKey();
         * final Term t = e.getValue();
         * if (t == null) {
         * continue;
         * }
         * if (replaceMap.containsKey(pv)) {
         * newAtPres.remove(pv);
         * pv = (LocationVariable) replaceMap.get(pv);
         * newAtPreVars.put(pv, atPreVars.get(e.getKey()));
         * }
         * newAtPres.put(pv, replaceVariablesInTerm(t));
         * }
         * final ProgramVariableCollection newVars =
         * new ProgramVariableCollection(vars.selfVar, vars.paramVars, vars.resultVar, vars.excVar,
         * newAtPreVars, newAtPres, vars.atBeforeVars, vars.atBefores);
         *
         *
         * var newTerms = spec.terms().map(this::replaceVariablesInTerm);
         * var newSpec = new SpecificationRepository.JmlStatementSpec(newVars, newTerms);
         *
         * services.getSpecificationRepository().addStatementSpec(x, newSpec);
         *
         * /*
         * if (!newAtPres.equals(vars.atPres)) {
         * changed();
         * }
         * doDefaultAction(x);
         */
        handleJmlStatements(x, SetStatement::new);
    }

    public <T extends Statement> void handleJmlStatements(T x, Function<T, T> cloner) {
        var spec = Objects.requireNonNull(
            services.getSpecificationRepository().getStatementSpec(x));

        ProgramVariableCollection vars = spec.vars();
        Map<LocationVariable, JTerm> atPres = vars.atPres;
        Map<LocationVariable, JTerm> newAtPres = new LinkedHashMap<>(atPres);
        Map<LocationVariable, LocationVariable> atPreVars = vars.atPreVars;
        Map<LocationVariable, LocationVariable> newAtPreVars = new LinkedHashMap<>(atPreVars);

        for (Entry<LocationVariable, JTerm> e : atPres.entrySet()) {
            LocationVariable pv = e.getKey();
            final JTerm t = e.getValue();
            if (t == null) {
                continue;
            }

            if (replaceMap.containsKey(pv)) {
                newAtPres.remove(pv);
                pv = replaceMap.get(pv);
                newAtPreVars.put(pv, atPreVars.get(e.getKey()));
            }
            newAtPres.put(pv, replaceVariablesInTerm(t));
        }
        final ProgramVariableCollection newVars =
            new ProgramVariableCollection(vars.selfVar, vars.paramVars, vars.resultVar, vars.excVar,
                newAtPreVars, newAtPres, vars.atBeforeVars, vars.atBefores);


        var newTerms = spec.terms().map(this::replaceVariablesInTerm);
        var newSpec = new SpecificationRepository.JmlStatementSpec(newVars, newTerms);

        var c = cloner.apply(x);
        services.getSpecificationRepository().addStatementSpec(c, newSpec);

        /*
         * if (!newAtPres.equals(vars.atPres)) {
         * changed();
         * }
         */
        doDefaultAction(c);
        changed();
    }

}
