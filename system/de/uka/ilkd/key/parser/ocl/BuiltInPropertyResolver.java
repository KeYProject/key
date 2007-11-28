// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.parser.ocl;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IteratorOfLogicVariable;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.AbstractCollectionSort;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.CollectionSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.CreatedAttributeTermFactory;
import de.uka.ilkd.key.util.Debug;



/**
 * Resolves built-in ocl property calls.
 */
class BuiltInPropertyResolver implements PropertyResolver {
    
    private static final TermFactory tf = TermFactory.DEFAULT;
    private static final TermBuilder tb = TermBuilder.DF;
    
    private static final CreatedAttributeTermFactory createdFactory
            = CreatedAttributeTermFactory.INSTANCE;
    private static final Term trueTerm = tb.tt();
    private static final Term falseTerm = tb.ff();
    
    private final Services services;
    
    private ParsableVariable excVar;
    
    public BuiltInPropertyResolver(Services services, ParsableVariable excVar) {
        this.services = services;
        this.excVar   = excVar;
    }

    
    private Term replaceVar(LogicVariable lv1, LogicVariable lv2, Term term) {
        Map map = new HashMap();
        map.put(lv1, lv2);
        OpReplacer or = new OpReplacer(map);
        return or.replace(term);
    }
    
    
    private void raiseError(String message) throws OCLTranslationError {
    	throw new OCLTranslationError("OCL Parser Error (PropertyResolver): " + message);
    }

    
    public OCLEntity resolve(OCLEntity receiver,
                             String name, 
                             OCLParameters parameters) throws OCLTranslationError {
        //allInstances---------------------------------------------------------
        if(name.equals("allInstances")) {
            if(!receiver.isType() 
               || parameters == null
               || !parameters.getDeclaredVars().isEmpty()
               || !parameters.getEntities().isEmpty()) {
                return null;
            }

            return new OCLEntity(new OCLCollection(receiver.getSort(), services));
        }
        
        
        //quantifiers----------------------------------------------------------
        if(name.equals("forAll") || name.equals("exists")) {
            if(!receiver.isCollection() 
               || parameters == null
               || parameters.getDeclaredVars().isEmpty()
               || parameters.getEntities().size() != 1) {
                return null;
            }
            
            Quantifier q;
            Junctor j;
            if(name.equals("forAll")) {
                q = Op.ALL;
                j = Op.IMP;
            } else {
                q = Op.EX;
                j = Op.AND;
            }
            
            Term restrictions = trueTerm;
            IteratorOfLogicVariable it 
                    = parameters.getDeclaredVars().iterator();
            while(it.hasNext()) {
                Term t = replaceVar(receiver.getCollection().getPredVar(),
                                    it.next(),
                                    receiver.getCollection().getPredicativeRestriction());
                restrictions = tf.createJunctorTermAndSimplify(Op.AND,
                                                               restrictions,
                                                               t);
            }
            
            Term subTerm 
                = tf.createJunctorTermAndSimplify(j,
                                                  restrictions,
                                                  parameters.getEntities().head().getTerm());
            Term resTerm = createdFactory.createCreatedNotNullQuantifierTerm(
                            services,
                            q,
                            parameters.getDeclaredVars().toArray(),
                            subTerm);
            
            return new OCLEntity(resTerm);
        }
        
        
        //select/reject--------------------------------------------------------
        if(name.equals("select") || name.equals("reject")) {
            if(!receiver.isCollection() 
               || parameters == null
               || parameters.getDeclaredVars().size() != 1
               || parameters.getEntities().size() != 1) {
                return null;
            }

            //Replace all occurrences of the new selectorVar with the 
            //appropriate collectionVar
            Term selectTerm = replaceVar(parameters.getDeclaredVars().head(), 
                                         receiver.getCollection().getPredVar(),
                                         parameters.getEntities().head().getTerm());
            

            if (name.equals("reject")) {
                selectTerm = tf.createJunctorTerm(Op.NOT,selectTerm);
            }
            
            LogicVariable selectVar = receiver.getCollection().getPredVar();
                        
            OCLCollection resCollection = receiver.getCollection().select(selectVar, selectTerm);
            
            return new OCLEntity(resCollection);            
        }
        
        
        //collect--------------------------------------------------------------
        if(name.equals("collect")) {
            if(!receiver.isCollection()
               || parameters == null
               || parameters.getDeclaredVars().size() > 1
               || parameters.getEntities().size() != 1) {
                return null;
            }
            
            Term collectTerm = parameters.getEntities().head().getTerm();
            
            if (collectTerm==null) {
            	// collectTerm was a collection
            	raiseError("Automatic flattening only supported for navigation over associations!");

            	// System.out.println(parameters.getEntities().head().getCollection());
            	//OCLCollection result = receiver.getCollection().collect(services,
            	//		parameters.getEntities().head().getCollection());
            	//return new OCLEntity(result);
            	
            }
            
            if(!parameters.getDeclaredVars().isEmpty()) {
                collectTerm = replaceVar(parameters.getDeclaredVars().head(),
                                         receiver.getCollection().getPredVar(),
                                         collectTerm);
            }

            OCLCollection result = receiver.getCollection().collect(services, collectTerm);
            
            return new OCLEntity(result);
        } 
        
        
        //includes/excludes----------------------------------------------------
        if(name.equals("includes") || name.equals("excludes")) {
            if(!receiver.isCollection()
               || parameters == null
               || !parameters.getDeclaredVars().isEmpty()
               || parameters.getEntities().size() != 1) {
                return null;
            }
            
            Term opTerm 
                = tf.createEqualityTerm(receiver.getCollection().getPredVarAsTerm(),
                                        parameters.getEntities().head().getTerm());
            
            Quantifier q;
            Junctor j;
            if(name.equals("excludes")) {
                opTerm = tf.createJunctorTerm(Op.NOT,opTerm);
                q = Op.ALL;
                j = Op.IMP;
            } else {
                q = Op.EX;
                j = Op.AND;
            }
            
            opTerm = tf.createJunctorTermAndSimplify(
                            j,
                            receiver.getCollection().getPredicativeRestriction(),
                            opTerm);
            
            LogicVariable[] vars = {receiver.getCollection().getPredVar()};
            Term resTerm = createdFactory.createCreatedNotNullQuantifierTerm(
                            services,
                            q,
                            vars,
                            opTerm);
            
            return new OCLEntity(resTerm);
        }
        
        
        //isEmpty/notEmpty-----------------------------------------------------
        if(name.equals("isEmpty") || name.equals("notEmpty")) {
            if(!receiver.isCollection()
               || parameters == null
               || !parameters.getDeclaredVars().isEmpty()
               || !parameters.getEntities().isEmpty()) {
                return null;
            }
            
            Quantifier q;
            Junctor j;
            Term opTerm;
            if(name.equals("isEmpty")) {
                q = Op.ALL;
                j = Op.IMP;
                opTerm = falseTerm;
            } else {
                q = Op.EX;
                j = Op.AND;
                opTerm = trueTerm;
            }
                            
            opTerm = tf.createJunctorTerm(
                            j,
                            receiver.getCollection().getPredicativeRestriction(),
                            opTerm);
            
            LogicVariable[] vars = {receiver.getCollection().getPredVar()};
            Term resTerm = createdFactory.createCreatedNotNullQuantifierTerm(
                            services,
                            q,
                            vars,
                            opTerm);
            
            return new OCLEntity(resTerm);
        }
        

        //isUnique-------------------------------------------------------------
        if(name.equals("isUnique")) {
            if(!receiver.isCollection() 
               || parameters == null
               || parameters.getDeclaredVars().size() != 1
               || parameters.getEntities().size() != 1) {
                return null;
            }
                        
            Term restrictions = trueTerm;
            LogicVariable temp = parameters.getDeclaredVars().head();
            LogicVariable lv1 
                    = new LogicVariable(new Name(temp.name()+"_1"),temp.sort());    
            LogicVariable lv2 
                    = new LogicVariable(new Name(temp.name()+"_2"),temp.sort());
            
            Term t1 = replaceVar(receiver.getCollection().getPredVar(),
                                 lv1,
                                 receiver.getCollection().getPredicativeRestriction());
            Term t2 = replaceVar(receiver.getCollection().getPredVar(),
                                 lv2,
                                 receiver.getCollection().getPredicativeRestriction());

            restrictions = tf.createJunctorTermAndSimplify(Op.AND,
                    t1,
                    t2);

            t1 = replaceVar(temp,
                            lv1,
                            parameters.getEntities().head().getTerm());
            t2 = replaceVar(temp,
                            lv2,
                            parameters.getEntities().head().getTerm());

            restrictions = tf.createJunctorTermAndSimplify(Op.AND,
                    restrictions,
                    tf.createEqualityTerm(t1,t2));
            
            t1 = tf.createVariableTerm(lv1);
            t2 = tf.createVariableTerm(lv2);
            
            Term subTerm 
                = tf.createJunctorTermAndSimplify(Op.IMP,
                                                  restrictions,
                                                  tf.createEqualityTerm(t1,t2));
            Term resTerm = createdFactory.createCreatedNotNullQuantifierTerm(
                            services,
                            Op.ALL,
                            new LogicVariable[]{lv1,lv2},
                            subTerm);
            
            return new OCLEntity(resTerm);

        }


        //size/sum/count--------------------------------------------------------------
        if(name.equals("size") ||
           name.equals("sum")  ||
           name.equals("count")) {
            
            if(!receiver.isCollection()
               || parameters == null
               || parameters.getDeclaredVars().size() > 0
               || parameters.getEntities().size() != 0) {
                return null;
            }

            CollectionSort ssort = FunctionFactory.getCollectionSort(
                    receiver.getSort(),
                    receiver.getCollection().getCollectionType());
            
            assert ssort!=null;
            
            Function f = (Function) services.getNamespaces().functions().lookup(
                    new Name(ssort.name().toString()+"::"+name));  
            
            return new OCLEntity(
                    tf.createFunctionTerm(
                            f,
                            receiver.getCollection().getFunctionalRestriction()));
        } 
                        

        //oclIsKindOf------------------------------------------------------------
        if(name.equals("oclIsKindOf")) {
            if(!receiver.isTerm() 
               || parameters == null
               || !parameters.getDeclaredVars().isEmpty()
               || !(parameters.getEntities().size() == 1)
               || !(parameters.getEntities().head().isType())) {
                return null;
            }
            
            Function instance = (Function) services.getNamespaces().functions().lookup(
                    new Name(parameters.getEntities().head().getType().getFullName()+"::instance"));
            
            Term result = tf.createFunctionTerm(instance,receiver.getTerm());
            
            return new OCLEntity(result);
        }

        
        //oclIsTypeOf------------------------------------------------------------
        if(name.equals("oclIsTypeOf")) {
            if(!receiver.isTerm() 
               || parameters == null
               || !parameters.getDeclaredVars().isEmpty()
               || !(parameters.getEntities().size() == 1)
               || !(parameters.getEntities().head().isType())) {
                return null;
            }
            
            Function instance = (Function) services.getNamespaces().functions().lookup(
                    new Name(parameters.getEntities().head().getType().getFullName()+"::exactInstance"));
            
            Term result = tf.createFunctionTerm(instance,receiver.getTerm());
            
            return new OCLEntity(result);
        }

        
        //oclAsType------------------------------------------------------------
        if(name.equals("oclAsType")) {
            if(!receiver.isTerm() 
               || parameters == null
               || !parameters.getDeclaredVars().isEmpty()
               || !(parameters.getEntities().size() == 1)
               || !(parameters.getEntities().head().isType())) {
                return null;
            }
            
            Term result = tf.createCastTerm(
                    (AbstractSort)parameters.getEntities().head().getSort(),
                    receiver.getTerm());
            
            return new OCLEntity(result);
        }

        
        //get (array access)------------------------------------------------------------
        if(name.equals("get")) {
            if(!receiver.isTerm() 
               || parameters == null
               || !parameters.getDeclaredVars().isEmpty()
               || !(parameters.getEntities().size() == 1)
               //|| !parameters.getEntities().head().getTerm().sort().name().toString().equals("int")
               //|| !(receiver.getSort() instanceof ArraySort)#
               ) {
                return null;
            }
            
            Term res = tf.createArrayTerm(
                    ArrayOp.getArrayOp(receiver.getSort()),
                    receiver.getTerm(),
                    parameters.getEntities().head().getTerm());
            
            return new OCLEntity(res);
        }
        
        //signals (exception-handling)--------------------------------------------------
        if(name.equals("signals")) {
            if(parameters == null
               || !parameters.getDeclaredVars().isEmpty()
               || !(parameters.getEntities().size() == 1)
               || !parameters.getEntities().head().isType()
            ) {
            	return null;
            }
            
            Sort excSort = parameters.getEntities().head().getType().getSort();
            Function instance = (Function) services.getNamespaces().functions().lookup(
                    new Name(excSort.name().toString()+"::instance"));  
            
            Term res = tb.and(
            		tb.not(tb.equals(tb.var(excVar),tb.NULL(services))),
            		tb.equals(tb.func(instance,tb.var(excVar)),tb.TRUE(services)));
            
            return new OCLEntity(res);
            
        }
        
        // modulo operation
        if (name.equals("mod")) {
            final IntegerLDT integerLDT = services.getTypeConverter().
                            getIntegerLDT();
            final Sort integerSort = integerLDT.targetSort();           
            if (!receiver.isTerm() 
                   || parameters == null 
                   || !(parameters.getEntities().size() == 1) 
                   || !(receiver.getSort().extendsTrans(integerSort)) 
                   || !(parameters.getEntities().head().getSort().extendsTrans(integerSort))) {                            
                return null;
            }
            return new OCLEntity(tb.func(integerLDT.getArithModulo(), 
                    receiver.getTerm(), 
                    parameters.getEntities().head().getTerm()));
        }

        // div operation
        if (name.equals("div")) {
            final IntegerLDT integerLDT = services.getTypeConverter().
                            getIntegerLDT();
            final Sort integerSort = integerLDT.targetSort();           
            if (!receiver.isTerm() 
                   || parameters == null 
                   || !(parameters.getEntities().size() == 1) 
                   || !(receiver.getSort().extendsTrans(integerSort)) 
                   || !(parameters.getEntities().head().getSort().extendsTrans(integerSort))) {                            
                return null;
            }
            return new OCLEntity(tb.func(integerLDT.getArithDivision(), 
                    receiver.getTerm(), 
                    parameters.getEntities().head().getTerm()));
        }

/*
 * TODO
 * 
        //asSet------------------------------------------------------------
        if(name.equals("asSet")) {
            if(!receiver.isCollection()) {
                return null;
            }
            
            return new OCLEntity(receiver.getCollection().asSet());
        }


        //asBag------------------------------------------------------------
        if(name.equals("asBag")) {
            if(!receiver.isCollection()) {
                return null;
            }
            
            return new OCLEntity(receiver.getCollection().asBag());
        }

        
        //asSequence------------------------------------------------------------
        if(name.equals("asSequence")) {
            if(!receiver.isCollection()) {
                return null;
            }
            
            return new OCLEntity(receiver.getCollection().asSequence());
        }
*/
        
        return null;
    }

    
    public boolean needVarDeclaration(String propertyName) {
        return (propertyName.equals("forAll") 
         || propertyName.equals("exists") 
         || propertyName.equals("select")
         || propertyName.equals("reject")
         || propertyName.equals("collect")
         || propertyName.equals("isUnique"));
    }    
}
