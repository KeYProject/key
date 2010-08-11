// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/*
 * Created on Apr 14, 2005
 */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ClassInstanceSortImpl;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This metaconstruct tries to statically determine whether an array component
 * assignment is safe, i.e. does not lead to an <code>ArrayStoreException</code>
 * Currently it makes use of a strong closed world assumption which could be relaxed
 * (of course by loss of power) to a version wo closed world asssumptions making
 * use of the final modifier of classes.
 * TODO: add features for multi-dimensional arrays 
 */
public class ArrayStoreStaticAnalyse extends AbstractMetaOperator {

    /**
     * creates this metaconstruct
     */
    public ArrayStoreStaticAnalyse() {
        super(new Name("#arrayStoreStaticAnalyse"), 1);
    }

    private ImmutableList<KeYJavaType> determineDynamicTypes(ClassInstanceSortImpl s,
            Services serv) {        
        final KeYJavaType keYJavaType = serv.getJavaInfo().getKeYJavaType(s);
        final ImmutableList<KeYJavaType> result = serv.getJavaInfo().getAllSubtypes(keYJavaType);
       
        return result.prepend(keYJavaType);
    }

    /**
     *
     * tests if the given sorts and all their subsorts are assignment
     * compatible or not. 
     * <tt> null </tt> is returned if some are and others are not 
     */
    private Term assignmentCompatible
    	(ClassInstanceSortImpl arrayElementSort,
    	        ClassInstanceSortImpl elementSort, Services serv) {
        final Iterator<KeYJavaType> elementDynamicTypesIt = determineDynamicTypes(
                elementSort, serv).iterator();
        final ImmutableList<KeYJavaType> arrayElementDynamicTypes = determineDynamicTypes(
                arrayElementSort, serv);

        boolean assignmentCompatible = true;
        boolean assignmentCompatibleSet = false;
        
        while (elementDynamicTypesIt.hasNext()) {
            final Iterator<KeYJavaType> arrayElementDynamicTypesIt = 
                arrayElementDynamicTypes.iterator();
            final Sort dynamicElementSort = elementDynamicTypesIt.next().getSort();
            boolean extTrans = false;           
            while (arrayElementDynamicTypesIt.hasNext()) {
                final Sort arrayElementDynamicSort = 
                    arrayElementDynamicTypesIt.next().getSort();
                extTrans = dynamicElementSort.extendsTrans(arrayElementDynamicSort);                

                if (assignmentCompatibleSet && extTrans != assignmentCompatible) {
                    // in this case we cannot say anything
                    // at least not true or false
                    // may be return later a formula
                    return null;
                }
                assignmentCompatible = assignmentCompatible && extTrans;
                assignmentCompatibleSet = true;
            }           
        }

        final TermFactory tf = TermFactory.DEFAULT;
        return assignmentCompatible ? tf.createJunctorTerm(Op.TRUE) : tf
                .createJunctorTerm(Op.FALSE);
    }

    
    
    /**    
     * tries to determine whether the predicate "arrayStoreValid" is true or 
     * false using type analysis. It makes some strong closed world assumptions.
     * A weaker version without closed world assumption is possible making use of
     * the final modifier of classes.
     * It assumes that teh first argumnet of <tt>arrayStoreValid</tt> is not 
     * equal to <tt>null</tt>
     */
    public Term calculate(Term term, SVInstantiations svInst, 
            Services services) {
        // term.sub(0) is predicate arrayStoreCondition
        final Term array = term.sub(0).sub(0);
        final Term element = term.sub(0).sub(1);

        final JavaInfo ji = services.getJavaInfo();
        
        if (!(array.sort() instanceof ArraySort) || 
                ji.isAJavaCommonSort(array.sort()) ||
                ji.isAJavaCommonSort(element.sort())) {
            return term.sub(0);        
        }

        final ArraySort arraySort = (ArraySort) array.sort();
        final Sort arrayElementSort = arraySort.elementSort();
        final Sort elementSort = element.sort();
        if (arrayElementSort instanceof ClassInstanceSortImpl
                && elementSort instanceof ClassInstanceSortImpl) {
            final Term result = assignmentCompatible(
                    (ClassInstanceSortImpl) arrayElementSort,
                    (ClassInstanceSortImpl) elementSort, services);
            return result == null ? term.sub(0) : result;
        } else if (arrayElementSort instanceof PrimitiveSort) {
            if (!(elementSort instanceof PrimitiveSort)) {
                return TermBuilder.DF.ff();
            } else {
                final Sort abstractInt = services.getTypeConverter().getIntegerLDT().targetSort();
                if (arrayElementSort.extendsTrans(abstractInt) && elementSort.extendsTrans(abstractInt)) {
                    return TermBuilder.DF.tt();
                }
                return TermBuilder.DF.ff();
            }
        }

        return term.sub(0);
    }

}
