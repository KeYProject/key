// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rule.metaconstruct;

import java.lang.reflect.InvocationTargetException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * The meta operator inserting the proof obligation for the <tt>inReachableState</tt>
 * predicate
 * @see de.uka.ilkd.key.rule.metaconstruct.InReachableStatePOBuilder
 */
public class CreateInReachableStatePO extends AbstractMetaOperator {

    private final Class<? extends AbstractInReachableStatePOBuilder> poBuilder;

    public CreateInReachableStatePO(String name, Class<? extends AbstractInReachableStatePOBuilder> builder) {
        super(new Name(name), 1);
        this.poBuilder = builder;
    }
    
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }
       
    public Term calculate(Term term, SVInstantiations svInst, Services services) {   
	AbstractInReachableStatePOBuilder po;
        try {
	    po = poBuilder.getConstructor(Services.class).newInstance(services);
        } catch (IllegalArgumentException e) {
	    e.printStackTrace();
	    throw e;
        } catch (SecurityException e) {
	    e.printStackTrace();
	    throw e;
        } catch (InstantiationException e) {
	    e.printStackTrace();
	    throw (RuntimeException)new RuntimeException().initCause(e);
        } catch (IllegalAccessException e) {
	    e.printStackTrace();
	    throw (RuntimeException)new RuntimeException().initCause(e);
        } catch (InvocationTargetException e) {
	    e.printStackTrace();
	    throw (RuntimeException)new RuntimeException().initCause(e);
        } catch (NoSuchMethodException e) {
	    e.printStackTrace();
	    throw (RuntimeException)new RuntimeException().initCause(e);
        }
      
        return po.generatePO(term.sub(0));       
    }
    
   
}
