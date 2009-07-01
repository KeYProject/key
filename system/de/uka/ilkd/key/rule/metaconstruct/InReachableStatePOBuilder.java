// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.explicitheap.ExplicitHeapConverter;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.IteratorOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.SLListOfKeYJavaType;
import de.uka.ilkd.key.java.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.updatesimplifier.ArrayOfAssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.util.Debug;

/**
 * generates the proof obligation establishing that a given state describes a
 * legal pointer structure, i.e. that serveral system invariants are satisfied,
 * like no created object references a non-created one.
 */
public class InReachableStatePOBuilder {
    
    private static final TermBuilder TB = TermBuilder.DF;
    private static final ExplicitHeapConverter EHC = ExplicitHeapConverter.INSTANCE;

    private final UpdateFactory uf;
    private final Services services;
    private final Sort intSort;
    private final ProgramVariable created;
    private final Term TRUE;
    private final Term FALSE;
    private final ProgramVariable arraylength;

    public InReachableStatePOBuilder(Services services) {
        uf = new UpdateFactory(services, new UpdateSimplifier());
        this.services = services;
        this.intSort = services.getTypeConverter().getIntegerLDT().targetSort();
        this.created =
                services.getJavaInfo().getAttribute(
                        ImplicitFieldAdder.IMPLICIT_CREATED,
                        services.getJavaInfo().getJavaLangObject());
        this.arraylength = services.getJavaInfo().getArrayLength();
        this.TRUE = TB.TRUE(services);
        this.FALSE = TB.FALSE(services);
    }

    /**
     * Generates an optimized proof obligation, which is true if the state
     * described by update <tt>U</tt> in
     * <tt>updateInReachableState:=U(<tt>inReachableState</tt>)</tt> leads
     * to a legal pointer structure reachable from the current state.
     */
    public Term generatePO(Term updateInReachableState) {
/*XXX
        if (!(updateInReachableState.op() instanceof IUpdateOperator)) {
            return updateInReachableState;
        }

        final IUpdateOperator updateOp =
                (IUpdateOperator) updateInReachableState.op();
        if (updateOp instanceof AnonymousUpdate) {
            return updateInReachableState;
        }
        final Update update = Update.createUpdate(updateInReachableState);

        ListOfTerm conjunctions = SLListOfTerm.EMPTY_LIST;
        final ArrayOfAssignmentPair pairs = update.getAllAssignmentPairs();

        for (int i = 0; i < pairs.size(); i++) {
            final AssignmentPair pair = pairs.getAssignmentPair(i);
            final Location loc = pair.location();

            Term result = null;
            if (loc instanceof ProgramVariable && loc.sort() != Sort.NULL) {
                final ProgramVariable pv = (ProgramVariable) loc;
                if (pv.isStatic()) {
                    if (pv.sort() instanceof ObjectSort) {
                        result = staticFieldLiveRef(update, pair);
                        if(EnumClassDeclaration.isEnumConstant(pv))
                            result = enumConstantPO(pv, update);
                    } else { // all implicit field are currently no reference
                        // fields
                        final ObjectSort containerType =
                                (ObjectSort) pv.getContainerType().getSort();
                        ProgramVariable[] implicitFields =
                                new ProgramVariable[] {
                                        cErroneous(containerType),
                                        cInitialized(containerType),
                                        cInInit(containerType),
                                        cPrepared(containerType),
                                        ntc(containerType) };

                        if (pv == implicitFields[4]) {
                            result = nextToCreateUpdatedSafely(update, pv);
                            if (pv.getContainerType().getJavaType() instanceof EnumClassDeclaration) {
                                result = TB.and(result, addNextToCreateEnumPO(pv, update));
                            }
                        } else {
                            // if one of these fields is updated we need an
                            // additional axiom
                            boolean additionalAxiom = true;
                            if (pv == implicitFields[0]) {
                                result =
                                        classErroneousUpdateIRSConform(update,
                                                implicitFields);
                            } else if (pv == implicitFields[1]) {
                                result =
                                        classInitializedUpdateIRSConform(
                                                update, implicitFields);
                            } else if (pv == implicitFields[2]) {
                                result =
                                        classInitInProgressUpdateIRSConform(
                                                update, implicitFields);
                            } else {
                                additionalAxiom = false;
                            }
                            if (additionalAxiom) {
                                // in <tt>inReachableState</tt>, if a class is
                                // neither initialized, nor inInitialization,
                                // nor
                                // erroneous (yes, objects of erroneous classes
                                // can exist) than no objects
                                // are created
                                final Term notErroneous =
                                        TB.equals(TB.var(implicitFields[0]), FALSE);
                                final Term notInitialized =
                                        TB.equals(TB.var(implicitFields[1]), FALSE);
                                final Term notInInit =
                                        TB.equals(TB.var(implicitFields[2]), FALSE);
                                final Term ntcIsZero =
                                        TB.equals(TB.var(implicitFields[4]),
                                                TB.zero(services));
                                result =
                                        TB.and(update(update, TB.imp(TB.and(TB.and(
                                                notErroneous, notInitialized),
                                                notInInit), ntcIsZero)), result);
                            }
                        }
                    }
                } else {
                    Debug.assertTrue(!pv.isMember());
                }
            } else if (loc instanceof AttributeOp) {
                final ProgramVariable pv =
                        (ProgramVariable) ((AttributeOp) loc).attribute();
                final Term refPrefix =
                        ((AttributeOp) loc).referencePrefix(pair.locationAsTerm());

                if (refPrefix.sort() != Sort.NULL) {
                    if (loc.sort() instanceof ObjectSort) {
                        final LogicVariable[] vPre = atPre(pair);
                        final Term[] tPre = var(vPre);
                        final Term preAx = preAx(tPre, pair.locationSubs());
                        result =
                                update(update, TB.imp(TB.equals(
                                        TB.dot(tPre[0], created), TRUE),
                                        createdOrNull(dot(tPre,
                                                (AttributeOp) loc))));
                        result = TB.all(vPre, TB.imp(preAx, result));
                    } else if (pv == created) {
                        if (refPrefix.op() instanceof SortDependingFunction
                                && ((SortDependingFunction) refPrefix.op()).getKind().equals(
                                        AbstractSort.OBJECT_REPOSITORY_NAME)) {
                            result =
                                    createdInvariantForReposInstance(update,
                                            refPrefix);
                        } else {
                            return updateInReachableState;
                        }
                    } else if (pv == arraylength) {
                        result = arrayLengthIsIRSConform(refPrefix, update);
                    }
                }
            } 
            else if (loc instanceof ArrayOp) {
                final Sort elementSort =
                        ((ArraySort) ((ArrayOp) loc).arraySort()).elementSort();
                if (elementSort instanceof ObjectSort) {
                    final LogicVariable[] vPre = atPre(pair);
                    final Term[] tPre = var(vPre);
                    final Term preAx = preAx(tPre, pair.locationSubs());

                    // a@pre[i@pre]
                    final Term atPreArrayTerm = array((ArrayOp) loc, tPre);

                    result =
                            update(update, TB.and(TB.imp(TB.equals(
                                    TB.dot(tPre[0], created), TRUE),
                                    createdOrNull(atPreArrayTerm)),
                                    arrayStoreValid(tPre[0], atPreArrayTerm)));

                    result = TB.all(vPre, TB.imp(preAx, result));
                }
            }
            if (result != null) {
                // take care of quantified updates
                result = quanUpdateClosure(pair, result);

                conjunctions = conjunctions.prepend(result);
            }
        }
        conjunctions = conjunctions.prepend(globalInvariants(update));
        final Term po = conjunction(conjunctions.iterator());

        // no free variables on top level
        Debug.assertTrue(po.freeVars().size() == 0);

        return po;*/
	assert false : "uh oh";
	return null;
    }

    private Term arrayStoreValid(Term arrayRef, Term arrayValue) {
        final Function f =
                (Function) services.getNamespaces().functions().lookup(
                        new Name("arrayStoreValid"));
        assert f != null : "ArrayStoreValid predicate not found.";
        return TB.func(f, arrayRef, arrayValue);
    }

    /**
     * in general an update of the <tt><created></tt> attribute would imply to
     * show a large formula in order to ensure that the
     * <tt>inReachableState</tt> property is preserved. In case of an update
     * pair <tt> T::<get>(idx).<created>=TRUE </tt> the formula can be
     * drastically reduced to <code>
     *    U( T::<get>(idx@pre).created = TRUE <-> 
     *         \exists int i; (i>=0               & 
     *                         i<T.<nextToCreate> & 
     *                         T::<get>(i) = T::<get>(idx@pre))    
     * </code>
     * (otherwise in case of <tt> o.<created>=TRUE </tt> one would need to
     * create the above formula for any subtype of <tt>o</t>'s static type)
     *  
     * This case is the most common case one usually gets. Other situations are rather artificially
     * and likely to be the result of faulty user interaction ;-)
     *  
     * @param update the Update to be checked
     * @param t_get the Term T::<get>(idx)
     * @return the relevant invariant
     */
//    private Term createdInvariantForReposInstance(Update update, Term t_get) {
//        Term result;
//        final SortDependingFunction get = ((SortDependingFunction) t_get.op());
//        final ObjectSort os = (ObjectSort) get.getSortDependingOn();
//        final LogicVariable lv = new LogicVariable(new Name("i"), intSort);
//
//        final Term idx = t_get.sub(0);
//        final LogicVariable idxPre = atPre(idx, 0);
//        final Term t_idxPre = TB.var(idxPre);
//
//        /*
//         * pair = (T::<get>(idx).created:=b) <code> U( T::<get>(idx@pre).created =
//         * TRUE <-> \exists int i; (i>=0 & i<T.<nextToCreate> & T::<get>(i) =
//         * T::<get>(idx@pre)) </code>
//         * 
//         */
//        final Term getPreIdx = TB.func(get, t_idxPre);
//
//        result =
//                TB.equiv(TB.equals(TB.dot(getPreIdx, created), TRUE), TB.ex(lv, TB.and(
//                        interval(TB.zero(services), TB.var(lv), TB.var(ntc(os))),
//                        TB.equals(TB.func(get, TB.var(lv)), getPreIdx))));
//
//        return TB.all(idxPre, TB.imp(TB.equals(idx, t_idxPre), update(update, result)));
//    }

    /**
     * for each assignment pair of an update a formula is created with the
     * relevant parts of the system invariants necessary to be shown to be
     * preserved. This method computes the closure of this formula wrt.
     * quantified updates.
     * 
     * @param pair
     *            the assignment pair used to determine the relevant parts of
     *            the system invariant
     * @param relevantInvariants
     *            the relevant part of the system invariants to be checked for
     *            preserveness
     * @return the closure of the relvant invariant formula
     */
    private Term quanUpdateClosure(final AssignmentPair pair,
            Term relevantInvariants) {
        Term closure = relevantInvariants;
        if (pair.nontrivialGuard()) {
            closure = TB.imp(pair.guard(), closure);
        }
        if (pair.boundVars().size() > 0) {
            closure =
                    TB.tf().createQuantifierTerm(Op.ALL, pair.boundVars(), closure);
        }
        return closure;
    }

    /**
     * conjunction of terms that state global invariants, i.e. which have to be
     * added to the generated proof obligation in each case and where no
     * optimisation is possible by disregarding pieces by looking on the
     * assignment pairs
     * 
     * @param update
     *            the Update to be checked to preserve <tt>inReachableState</tt>
     * @return global invariants
     */
//    private Term globalInvariants(Update update) {
//        return noObjectDeletion(update);
//    }

    /**
     * Generates a formula ensuring that an update (U) does not delete a former
     * created object. This created axiom is as follows: <code>
     *          \forall Object o; (o.<created> = TRUE -> U o.<created> = TRUE)
     *     </code>
     * 
     * @param update
     *            the Update U which is checked for object deletion
     * @return a formula that evaluates to true if the update does not delete
     *         objects
     */
//    private Term noObjectDeletion(Update update) {
//        final LogicVariable o =
//                new LogicVariable(new Name("o"),
//                        services.getJavaInfo().getJavaLangObjectAsSort());
//        final Term o_created = TB.equals(TB.dot(TB.var(o), created), TRUE);
//        return TB.all(o, TB.imp(o_created, update(update, o_created)));
//    }

    /**
     * Generates a formula checking that the given static field <tt>T.sv</tt>
     * references <tt>null</tt> or a created object. Let
     * <tt>pair=(T.sv := t)</tt> the method assumes that loc is a static field
     * of reference type ref (ref != Sort.NULL) and generates the following
     * formula <code>
     *          U(T.<initialized>=TRUE -> T.sv.<created>=TRUE | T.sv = null)
     * </code>
     * ensuring that the static field is only updated to a living object or null
     * 
     * @param update the
     *            Update U to be checked
     * 
     * @return a formula that evaluates to true iff the update U does not update
     *         the static field loc to an "illegal" value
     */
//    private Term staticFieldLiveRef(Update update, AssignmentPair pair) {
//        final ProgramVariable classInit =
//                services.getJavaInfo().getAttribute(
//                        ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED,
//                        (((ProgramVariable) pair.location())).getContainerType());
//        return update(update, TB.imp(TB.equals(TB.var(classInit), TRUE),
//                createdOrNull(pair.locationAsTerm())));
//    }

    /**
     * generates a formula that ensures that all ensuring that the updated field
     * <tt>T.<nextToCreate></tt> still satisfies its invariants namely that
     * its value
     * <ul>
     * <li>remains greater than or equals zero</li>
     * <li>that all created objects have an index between 0 and T.<nextToCreate>
     * </li>
     * </ul>
     * <code>
     *   U ( T.<nextToCreate> >= 0 )  
     *     &
     *    -- unoptimized \forall int i; (i>=0 & i < T.<nextToCreate> <-> T::<get>(i).<created>=TRUE)         
     *    -- optimized
     *        \forall int i; (i>=T.<nextToCreate> & i < U(T.<nextToCreate>) -> U(T::<get>(i).<created>=TRUE))
     *     )   
     *   &
     *   T.<nextToCreate> <= U (T.<nextToCreate>)    
     * </code>
     * 
     * @param update
     *            the update to be checked
     * @param pv
     *            the ProgramVariable representing <tt>T.<nextToCreate></tt>
     * @return a formula that evaluates to true if the update U does not destroy
     *         the system invariants of <tt>T.<nextToCreate></tt>
     */
//    private Term nextToCreateUpdatedSafely(final Update update,
//            final ProgramVariable pv) {
//        Term result;
//        final ObjectSort os = (ObjectSort) pv.getContainerType().getSort();
//        final LogicVariable iv = new LogicVariable(new Name("i"), intSort);
//
//        final Term updatedPV = update(update, TB.var(pv));
//
//        result = TB.geq(updatedPV, TB.zero(services), services);
//
//        final Term interval = interval(TB.var(pv), TB.var(iv), updatedPV);
//
//        result =
//                TB.and(result, TB.all(iv, TB.imp(interval, update(update, TB.equals(TB.dot(
//                        TB.func(rep(os), TB.var(iv)), created), TB.TRUE(services))))));
//
//        result = TB.and(result, TB.leq(TB.var(pv), updatedPV, services));
//
//        return result;
//    }

    /**
     * generate a formula that ensures that for an enum type <code>E</code> an
     * update <tt>E.&lt;nextToCreate&gt; := c</tt> satisfies the invariant for
     * an enum.
     * 
     * <p>
     * An enumerated type has (once the class has been initialised) a fixed
     * number of created elements #ntc(E) which may not be changed if in a
     * reachable state.
     * 
     * <p>
     * The value of #ntc(E) can be resolved by {@link EnumClassDeclaration}.
     * 
     * It has to be made sure that
     * 
     * <pre>
     * {U} (E.&lt;classInitialized&gt; = TRUE -&gt; E.&lt;nextToCreate&gt; = #ntc(E))
     * </pre>
     * 
     * @author mulbrich
     * @param pv
     *            the PV that must be the static nextToCreate-Field of an enum
     *            type
     * @param update the update U to prend
     * @return the formulae above, not null.
     */
    private Term addNextToCreateEnumPO(ProgramVariable pv, Update update) {
        assert pv.getContainerType().getJavaType() instanceof EnumClassDeclaration;
        assert pv == ntc((ObjectSort) pv.getContainerType().getSort());

        ObjectSort objSort = (ObjectSort) pv.getContainerType().getSort();
        ProgramVariable clInit = cInitialized(objSort);

        EnumClassDeclaration ed =
                (EnumClassDeclaration) pv.getContainerType().getJavaType();
        int count = ed.getNumberOfConstants();
        Term countLit =
                services.getTypeConverter().convertToLogicElement(
                        new IntLiteral(count));

        return update(update, TB.imp(TB.equals(TB.var(clInit), TB.TRUE(services)), TB.equals(
                TB.var(pv), countLit)));

    }

    /**
     * generate a formula that ensures that for any enum constant the repository
     * constraint is ensured.
     * 
     * <p>
     * If pv is an enum constant <code>E.pv</code>, than there is an index
     * <code>#index(pv)</code> for which the following has to be ensured:
     * 
     * <pre>
     *  {U} ( E.pv = E::&lt;get&gt;(#index(pv)) )
     * </pre>
     * 
     * @author mulbrich
     * @param pv
     *            PV to be ensured
     * @param update
     *            the update {U} to prepend the formula
     * @return the formula above, not null.
     */
    private Term enumConstantPO(ProgramVariable pv, Update update) {
        assert EnumClassDeclaration.isEnumConstant(pv);
        ObjectSort objSort = (ObjectSort) pv.getKeYJavaType().getSort();

        int index = EnumClassDeclaration.indexOf(pv);
        Term indexLit =
                services.getTypeConverter().convertToLogicElement(
                        new IntLiteral(index));

        return update(update, TB.equals(TB.var(pv), TB.func(rep(objSort), indexLit)));
    }
    
    /**
     * A class that is marked as erroneous is neither initialized nor is its
     * initialization in progress.
     * 
     * If a class is marked erroneous its subclasses are not allowed to be
     * initialized. It is sufficient to test this property for its direct
     * subclasses. As if ...TODO
     * 
     * Additionally: from an <tt>inReachableState</tt> state with a class C
     * marked erroneous, no state in <tt>inReachableState</tt> is reachable
     * where the same class is not erroneous
     * 
     * <code>
     *    U(C.<erroneous>   = TRUE -> (C.<classInitialized> = FALSE & 
     *                                 C.<initInProgress>   = FALSE)
     *    & 
     *    
     *    U(C.<erroneous>   = TRUE -> for all direct subtypes S of C: AND (S.<initialized> = FALSE) ) 
     *    
     *    &
     *    
     *    C.<erroneous>     = TRUE -> U(C.<erroneous> = TRUE)                      
     * </code>
     * 
     * @param update
     *            the Update describing the new state to be checked for the
     *            <tt>inReachableState</tt> property
     * @param implicitFields
     *            the ProgramVariables for the field C.<erroneous>, C.<initialized>,
     *            C.<initInProgress> and C.<nextToCreate> (in this order)
     * @return a formula that evaluates to true if erroneous has been updated by
     *         U in an <tt>inReachableState</tt> comforming way
     */
    private Term classErroneousUpdateIRSConform(Update update,
            ProgramVariable[] implicitFields) {

        final Term classErroneous = TB.equals(TB.var(implicitFields[0]), TRUE);

        Term result =
                classFieldUpdateConform(update, implicitFields[0],
                        implicitFields[1], implicitFields[2], null);

        final KeYJavaType currentType = implicitFields[0].getContainerType();
        final ListOfKeYJavaType directSubTypes = getDirectSubtypes(currentType);

        if (!directSubTypes.isEmpty()) {
            final IteratorOfKeYJavaType it = directSubTypes.iterator();
            Term subsNotInit = TB.tt();
            while (it.hasNext()) {
                final ProgramVariable subsCInitPV =
                        cInitialized((ObjectSort) it.next().getSort());
                subsNotInit = TB.and(subsNotInit, TB.equals(TB.var(subsCInitPV), FALSE));
            }
            result = TB.and(result, update(update, subsNotInit));
        }

        result =
                TB.and(result, TB.imp(classErroneous, update(update, classErroneous)));

        return result;
    }

    /**
     * A class that is being initialized is neither initialized nor erroneous.
     * <code>
     *    U(C.<initInProgress> = TRUE -> (C.<erroneous>        = FALSE & 
     *                                    C.<initialized>      = FALSE &
     *                                    C.<prepared>
     *           = TRUE)        
     * </code>
     *   @param update the Update describing the new state to be checked for the
     * <tt>
     * inReachableState
     * </tt>
     *   property
     *   @param implicitFields the ProgramVariables for the field 
     *      C.&lt;erroneous&gt;, C.&lt;initialized&gt;, C.&lt;initInProgress&gt; and C.&lt;nextToCreate&gt;
     *      (in this order)
     *   @return a formula that evaluates to true if erroneous has been updated by U in an
     * <tt>
     * inReachableState
     * </tt>
     *   comforming way
     * 
     */
    private Term classInitInProgressUpdateIRSConform(Update update,
            ProgramVariable[] implicitFields) {

        Term result =
                classFieldUpdateConform(update, implicitFields[2],
                        implicitFields[0], implicitFields[1], implicitFields[3]);

        return result;
    }

    /**
     * A class that is marked as initialized is neither initialized nor is its
     * initialization in progress.
     * 
     * If a class is initialized all its supertypes must be initialized, too. It
     * is sufficient to look at the direct supertypes as if they are initialized
     * all their supertypes are also initialized in the prestate (as it has the
     * <tt>inReachableState</tt> property) or their fields have been updated
     * and the formula ensuring this property for their supertypes will be (or
     * have been) created when looking at the other assignment pairs of the
     * update)
     * 
     * Additionally: from an <tt>inReachableState</tt> state with an
     * initialized class C, no state in <tt>inReachableState</tt> is reachable
     * where the same class is not initialized
     * 
     * <code>
     *    U(C.<initialized> = TRUE -> (C.<erroneous>        = FALSE & 
     *                                 C.<initInProgress>   = FALSE & 
     *                                 C.<prepared>
     *           = TRUE  )
     *      &amp;
     *      
     *      U(C.&lt;initialized&gt; = TRUE -&gt; for all direct supertypes S of C: AND (S.&lt;initialized&gt; = TRUE) ) 
     *      
     *      &amp;
     *      C.&lt;initialized&gt;   = TRUE -&gt; U(C.&lt;initialized&gt; = TRUE)                      
     * </code>
     *   @param update the Update describing the new state to be checked for the
     * <tt>
     * inReachableState
     * </tt>
     *   property
     *   @param implicitFields the ProgramVariables for the field 
     *      C.&lt;erroneous&gt;, C.&lt;initialized&gt;, C.&lt;initInProgress&gt;, C.&lt;prepared&gt; and C.&lt;nextToCreate&gt;
     *      (in this order)
     *   @return a formula that evaluates to true if erroneous has been updated by U in an
     * <tt>
     * inReachableState
     * </tt>
     *   comforming way
     * 
     */
    private Term classInitializedUpdateIRSConform(Update update,
            ProgramVariable[] implicitFields) {

        final Term classInitialized = TB.equals(TB.var(implicitFields[1]), TRUE);

        Term result =
                classFieldUpdateConform(update, implicitFields[1],
                        implicitFields[0], implicitFields[2], implicitFields[3]);
        // direct supertypes

        final ListOfKeYJavaType directSuperTypes =
                services.getJavaInfo().getDirectSuperTypes(
                        implicitFields[0].getContainerType());

        if (!directSuperTypes.isEmpty()) {
            final IteratorOfKeYJavaType it = directSuperTypes.iterator();
            Term superTypesInit = TB.tt();
            while (it.hasNext()) {
                final ProgramVariable superCInitPV =
                        cInitialized((ObjectSort) it.next().getSort());
                superTypesInit =
                        TB.and(superTypesInit, TB.equals(TB.var(superCInitPV), TRUE));
            }
            result =
                    TB.and(result, update(update, TB.imp(classInitialized,
                            superTypesInit)));
        }

        // reachable <tt>inReachableState</tt> state
        result =
                TB.and(result, TB.imp(classInitialized, update(update,
                        classInitialized)));

        return result;
    }

    /**
     * the length attribute of arrays is always creater or equal than zero
     * <code>
     *    \forall x; ((x = arrayReference & x!=null -> U(x.<created>=TRUE -> x.length >= 0)))
     * </code>
     */
//    private Term arrayLengthIsIRSConform(Term arrayReference, Update u) {
//        final LogicVariable preRef = atPre(arrayReference, 0);
//        return TB.all(preRef, TB.imp(TB.and(TB.equals(TB.var(preRef), arrayReference),
//                TB.not(TB.equals(TB.var(preRef), TB.NULL(services)))), update(u, TB.imp(
//                TB.equals(TB.dot(TB.var(preRef), created), TB.TRUE(services)), TB.geq(TB.dot(
//                        TB.var(preRef), arraylength), TB.zero(services), services)))));
//    }

    // helper method for class field pos

    /**
     * @param currentType
     */
    private ListOfKeYJavaType getDirectSubtypes(final KeYJavaType currentType) {
        ListOfKeYJavaType directSubTypes = SLListOfKeYJavaType.EMPTY_LIST;

        final JavaInfo javaInfo = services.getJavaInfo();
        final ListOfKeYJavaType allSubTypes =
                javaInfo.getAllSubtypes(currentType);

        final IteratorOfKeYJavaType subTypes = allSubTypes.iterator();
        while (subTypes.hasNext()) {
            final KeYJavaType subtype = subTypes.next();
            final ListOfKeYJavaType subsDirectSuper =
                    javaInfo.getDirectSuperTypes(subtype);
            if (subsDirectSuper.contains(currentType)) {
                directSubTypes = directSubTypes.prepend(subtype);
            }
        }
        return directSubTypes;
    }

    private Term classFieldUpdateConform(Update update, ProgramVariable fieldA,
            ProgramVariable fieldB, ProgramVariable fieldC,
            ProgramVariable fieldD) {

        final Term classA = TB.equals(TB.var(fieldA), TRUE);
        final Term classNotB = TB.equals(TB.var(fieldB), FALSE);
        final Term classNotC = TB.equals(TB.var(fieldC), FALSE);

        if (fieldD != null) {
            return update(update, TB.imp(classA, TB.and(TB.and(classNotB, classNotC),
                    TB.equals(TB.var(fieldD), TRUE))));
        }

        return update(update, TB.imp(classA, TB.and(classNotB, classNotC)));
    }

    // Helpers to build term
    private Term conjunction(IteratorOfTerm it) {
        Term result = TB.tt();
        while (it.hasNext()) {
            result = TB.and(result, it.next());
        }
        return result;
    }

    private Term update(Update update, Term target) {          
        return uf.prepend(update, target);
    }

//    private Term createdOrNull(final Term t_o_a) {
//        return TB.or(TB.equals(TB.dot(t_o_a, created), TRUE), TB.equals(t_o_a,
//                TB.NULL(services)));
//    }

    private ProgramVariable ntc(ObjectSort os) {
        return services.getJavaInfo().getAttribute(
                ImplicitFieldAdder.IMPLICIT_NEXT_TO_CREATE, os);
    }

    private ProgramVariable cInInit(ObjectSort os) {
        return services.getJavaInfo().getAttribute(
                ImplicitFieldAdder.IMPLICIT_CLASS_INIT_IN_PROGRESS, os);
    }

    private ProgramVariable cInitialized(ObjectSort os) {
        return services.getJavaInfo().getAttribute(
                ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, os);
    }

    private ProgramVariable cPrepared(ObjectSort os) {
        return services.getJavaInfo().getAttribute(
                ImplicitFieldAdder.IMPLICIT_CLASS_PREPARED, os);
    }

    private ProgramVariable cErroneous(ObjectSort os) {
        return services.getJavaInfo().getAttribute(
                ImplicitFieldAdder.IMPLICIT_CLASS_ERRONEOUS, os);
    }

    private Term interval(Term lower, Term i, Term upper) {
        return TB.and(TB.geq(i, lower, services), TB.lt(i, upper, services));
    }

    private Function rep(ObjectSort os) {
        return (Function) ((SortDefiningSymbols) os).lookupSymbol(AbstractSort.OBJECT_REPOSITORY_NAME);
    }

    /** creates an attribute term and takes care of shadowed attributes as well */
//    private Term dot(Term[] subs, AttributeOp op) {
//        return TB.tf().createAttributeTerm(op, subs);
//    }

    private Term[] var(LogicVariable[] v) {
        final Term[] result = new Term[v.length];
        for (int i = 0; i < result.length; i++) {
            result[i] = TB.var(v[i]);
        }
        return result;
    }

    private Term preAx(Term[] t1, Term[] t2) {
        Term result = TB.tt();
        for (int i = 0; i < t1.length; i++) {
            result = TB.and(result, TB.equals(t1[i], t2[i]));
        }
        return result;
    }
    
    private LogicVariable atPre(Term t, int idx) {        
        final Name name = 
            new Name(t.sort().name().toString().charAt(0)+""+idx+"irs");
        return new LogicVariable(name, t.sort());
    }

    private LogicVariable[] atPre(AssignmentPair pair) {
        final Term[] subs = pair.locationSubs();
        final LogicVariable[] result = new LogicVariable[subs.length];
        for (int i = 0; i < result.length; i++) {
            result[i] = atPre(subs[i], i);
        }
        return result;
    }
}
