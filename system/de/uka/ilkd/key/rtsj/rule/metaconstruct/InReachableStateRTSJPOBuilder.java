// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                          Universitaet Koblenz-Landau, Germany
//                          Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.rtsj.rule.metaconstruct;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.RTSJProfile;
import de.uka.ilkd.key.rule.metaconstruct.AbstractInReachableStatePOBuilder;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

/**
 * generates the proof obligation establishing that a given state describes a
 * legal pointer structure, i.e. that serveral system invariants are satisfied,
 * like no created object references a non-created one.
 */
public class InReachableStateRTSJPOBuilder extends
        AbstractInReachableStatePOBuilder {

    private final TermSymbol os;
    private final TermSymbol im;
    private final ProgramVariable ma;
    private final ProgramVariable stack;
    private final ProgramVariable parent;

    public InReachableStateRTSJPOBuilder(Services services) {
	super(services);

	assert ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof RTSJProfile;
	this.stack = services.getJavaInfo().getAttribute("stack",
		services.getJavaInfo().getJavaxRealtimeMemoryArea());
	this.parent = services.getJavaInfo().getAttribute("parent",
		services.getJavaInfo().getJavaxRealtimeMemoryArea());
	this.ma = services.getJavaInfo().getAttribute(
		ImplicitFieldAdder.IMPLICIT_MEMORY_AREA,
		services.getJavaInfo().getJavaLangObject());
	os = (TermSymbol) services.getNamespaces().functions()
	.lookup(new Name("outerScope"));
	im = (TermSymbol) services.getNamespaces().functions()
	.lookup(new Name("immortal"));
    }

    protected Term validateInstanceReferenceTypedFieldUpdate(boolean[] ax,
	    final Update update, final AssignmentPair pair, final Location loc,
	    final ProgramVariable pv) {
	Term result = super.validateInstanceReferenceTypedFieldUpdate(ax, update, pair, loc, pv);

	if (!pv.equals(parent) && !pv.equals(ma)) {
	    result = and(result, attrOuterRef(update, pv));
	}
	if (pv.equals(stack) || pv.equals(ma)) {
	    if (!ax[2]) {
		result = and(result, legalReferencesRemainLegal(update));
		ax[2] = true;
	    }
	    if (!ax[0]) {
		scopeAllocInOuterScope(update);
	    }
	    if ((pv.equals(stack)) && !ax[3]) {
		result = and(result, stackInjective(update));
		ax[3] = true;
	    }
	    if ((pv.equals(ma)) && !ax[1]) {
		scopeNotNull(update);
		ax[1] = true;
	    }
	}
	
	return result;
    }

    protected Term validateStaticReferenceTypedFieldUpdate(final Update update,
	    final AssignmentPair pair, final ProgramVariable pv) {
	Term result = super.validateStaticReferenceTypedFieldUpdate(update, pair, pv);

	return and(result, staticAttrImmortal(update, pv));
    }

    protected Term validateNextToCreateUpdate(boolean[] ax,
	    final Update update, final ProgramVariable pv,
	    final ObjectSort containerType) {
	
	Term result = super.validateNextToCreateUpdate(ax, update, pv, containerType);

	result = and(result, newObjectRefsLegal(update, containerType));

	if (containerType.extendsTrans(services.getJavaInfo()
		.getJavaxRealtimeMemoryArea().getSort())
		&& !ax[0]) {
	    scopeAllocInOuterScope(update);
	    ax[0] = true;
	}
	if (!ax[1]) {
	    scopeNotNull(update);
	    ax[1] = true;
	}
	if (containerType instanceof ArraySort
		&& ((ArraySort) containerType).elementSort() instanceof ObjectSort) {
	    result = and(result, arraySlotOuterRef(update, containerType));
	}
	return result;
    }


    protected Term validateArrayElementUpdate(final Update update,
	    final AssignmentPair pair, final Location loc, Term result) {
	final ArraySort arraySort = (ArraySort) ((ArrayOp) loc).arraySort();
	return and(super.validateArrayElementUpdate(update, pair, loc, result), 
		arraySlotOuterRef(update, arraySort));
    }

    /**
     * Generates a formula ensuring that the update does not lead to a state in
     * which a memory scope is allocated in one of its inner scopes The formula
     * is: \forall MemoryArea m; ((m.<created> = TRUE & outerScope(m.stack,
     * m.<memoryArea>.stack)) -> m=ImmortalMemory.instance
     * 
     * @param update
     * @return a formula that evaluates to true if no memory scope is allocated
     *         in one of its inner scopes
     */
    private Term scopeAllocInOuterScope(Update update) {
	final LogicVariable m = new LogicVariable(new Name("m"), services
	        .getJavaInfo().getJavaxRealtimeMemoryArea().getSort());
	final Term m_created = equals(dot(var(m), created), TRUE);
	return update(
	        update,
	        all(m,
	                imp(and(m_created,
	                        func(os, dot(var(m), stack),
	                                dot(dot(var(m), ma), stack))),
	                        equals(var(m),
	                                var(services
	                                        .getJavaInfo()
	                                        .getAttribute(
	                                                "instance",
	                                                services.getJavaInfo()
	                                                        .getJavaxRealtimeImmortalMemory()))))));
    }

    /**
     * 
     * @param update
     * @return a formula evaluating to true if each scope stack is referenced by
     *         at most one created scope.
     */
    private Term stackInjective(Update update) {
	final LogicVariable a = new LogicVariable(new Name("a"), services
	        .getJavaInfo().getJavaxRealtimeMemoryArea().getSort());
	final LogicVariable b = new LogicVariable(new Name("b"), services
	        .getJavaInfo().getJavaxRealtimeMemoryArea().getSort());
	final Term a_created = equals(dot(var(a), created), TRUE);
	final Term b_created = equals(dot(var(b), created), TRUE);
	final Term a_stackNotNull = not(equals(dot(var(a), stack),
	        NULL(services)));
	final Term a_b_stack_equal = equals(dot(var(a), stack),
	        dot(var(b), stack));
	Term[] premise = new Term[] { a_created, b_created, a_stackNotNull,
	        a_b_stack_equal };
	QuantifiableVariable[] qvs = new QuantifiableVariable[] { a, b };
	return update(update,
	        all(qvs, imp(and(premise), equals(var(a), var(b)))));
    }

    /**
     * 
     * @param update
     * @return the formula {update} \forall Object o; o.<created> = TRUE ->
     *         o.<memoryArea>!=null
     */
    private Term scopeNotNull(Update update) {
	final LogicVariable o = new LogicVariable(new Name("o"), services
	        .getJavaInfo().getJavaLangObjectAsSort());
	final Term o_created = equals(dot(var(o), created), TRUE);
	return update(
	        update,
	        all(o,
	                imp(o_created,
	                        not(equals(dot(var(o), ma), NULL(services))))));
    }

    /**
     * 
     * @param update
     * @param attr
     * @return the formula {update} \forall containertypeof(attr) o;
     *         (o.<created>=TRUE & o.attr!=null & o!=null) ->
     *         outerScope(o.attr.<memoryArea>.stack, o.<memoryArea>.stack)
     */
    private Term attrOuterRef(Update update, ProgramVariable attr) {
	final LogicVariable o = new LogicVariable(new Name("o"), attr
	        .getContainerType().getSort());
	final Term o_created = equals(dot(var(o), created), TRUE);
	final Term o_notNull = not(equals(var(o), NULL(services)));
	final Term attr_notNull = not(equals(dot(var(o), attr), NULL(services)));
	final Term osAttr = func(os, dot(dot(dot(var(o), attr), ma), stack),
	        dot(dot(var(o), ma), stack));
	return update(
	        update,
	        all(o,
	                imp(and(new Term[] { o_created, o_notNull, attr_notNull }),
	                        osAttr)));
    }

    /**
     * 
     * @param update
     * @param arraySort
     * @return the formula {update} \forall arraySort o; \forall int i;
     *         (o.<created>=TRUE & o.[i]!=null & o!=null) ->
     *         outerScope(o.[i].<memoryArea>.stack, o.<memoryArea>.stack)
     */
    Term arraySlotOuterRef(Update update, Sort arraySort) {
	final LogicVariable o = new LogicVariable(new Name("o"), arraySort);
	final LogicVariable i = new LogicVariable(new Name("i"), services
	        .getTypeConverter().getIntegerLDT().targetSort());
	final Term o_created = equals(dot(var(o), created), TRUE);
	final Term o_notNull = not(equals(var(o), NULL(services)));
	final Term arraySlot_notNull = not(equals(array(var(o), var(i)),
	        NULL(services)));
	final Term osArray = func(os,
	        dot(dot(array(var(o), var(i)), ma), stack),
	        dot(dot(var(o), ma), stack));
	return update(
	        update,
	        all(o,
	                all(i,
	                        imp(and(new Term[] { o_created, o_notNull,
	                                arraySlot_notNull }), osArray))));
    }

    private Term newObjectRefsLegal(Update u, ObjectSort s) {
	JavaInfo ji = services.getJavaInfo();
	ImmutableList<Field> fields = ji.getKeYProgModelInfo()
	        .getAllFieldsLocallyDeclaredIn(ji.getKeYJavaType(s));
	Iterator<Field> it = fields.iterator();
	Term result = tt();
	while (it.hasNext()) {
	    Field f = it.next();
	    if (f.getProgramVariable().sort() instanceof ObjectSort
		    && !((ProgramVariable) f.getProgramVariable()).isStatic()
		    && !(f.getProgramVariable().equals(parent) || f
		            .getProgramVariable().equals(ma))
		    && !((ProgramVariable) f.getProgramVariable()).isImplicit()) {
		result = and(
		        result,
		        attrOuterRef(u,
		                (ProgramVariable) f.getProgramVariable()));
	    }
	}
	if (s instanceof ArraySort
	        && ((ArraySort) s).elementSort() instanceof ObjectSort) {
	    result = and(result, arraySlotOuterRef(u, s));
	}
	return result;
    }

    /**
     * 
     * @param update
     * @return the formula \forall Object o1,o2; o1.<created>=TRUE &
     *         o2.<created>=TRUE & outerScope(o1.<memoryArea>.stack,
     *         o2.<memoryArea>.stack) ->
     *         {update}outerScope(o1.<memoryArea>.stack, o2.<memoryArea>.stack)
     */
    private Term legalReferencesRemainLegal(Update update) {
	final LogicVariable o1 = new LogicVariable(new Name("o1"), services
	        .getJavaInfo().getJavaLangObjectAsSort());
	final LogicVariable o2 = new LogicVariable(new Name("o2"), services
	        .getJavaInfo().getJavaLangObjectAsSort());
	final Term o1_created = equals(dot(var(o1), created), TRUE);
	final Term o2_created = equals(dot(var(o2), created), TRUE);
	final Term osO1O2 = func(os, dot(dot(var(o1), ma), stack),
	        dot(dot(var(o2), ma), stack));
	return all(
	        o1,
	        all(o2,
	                imp(and(new Term[] { o1_created, o2_created, osO1O2 }),
	                        update(update, osO1O2))));
    }

    private Term staticAttrImmortal(Update update, ProgramVariable attr) {
	final Term attr_notNull = not(equals(var(attr), NULL(services)));
	final Term attr_created = equals(dot(var(attr), created), TRUE);
	final Term attrImmortal = func(im, dot(dot(var(attr), ma), stack));
	return update(update,
	        imp(attr_notNull, and(attr_created, attrImmortal)));
    }
}
