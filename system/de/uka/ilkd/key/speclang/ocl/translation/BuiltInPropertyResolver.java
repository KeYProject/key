// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

package de.uka.ilkd.key.speclang.ocl.translation;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IteratorOfLogicVariable;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.CollectionSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.CreatedAttributeTermFactory;
import de.uka.ilkd.key.speclang.translation.SLResolverManager;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLExpressionResolver;
import de.uka.ilkd.key.speclang.translation.SLParameters;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;



/**
 * Resolves built-in ocl property calls.
 */
class BuiltInPropertyResolver extends SLExpressionResolver {
    
    private static final TermFactory tf = TermFactory.DEFAULT;
    private static final TermBuilder tb = TermBuilder.DF;
    
    private static final CreatedAttributeTermFactory createdFactory
            = CreatedAttributeTermFactory.INSTANCE;
    private static final Term trueTerm = tb.tt();
    private static final Term falseTerm = tb.ff();
    
    private final Services services;
    
    private ParsableVariable excVar;
    
    public BuiltInPropertyResolver(Services services, ParsableVariable excVar, SLResolverManager man) {
        super(services.getJavaInfo(), man);
        this.services = services;
        this.excVar   = excVar;
    }

    
    private Term replaceVar(LogicVariable lv1, LogicVariable lv2, Term term) {
        Map<LogicVariable, LogicVariable> map = 
            new LinkedHashMap<LogicVariable, LogicVariable>();
        map.put(lv1, lv2);
        OpReplacer or = new OpReplacer(map);
        return or.replace(term);
    }
    
    
    private void raiseError(String message) throws SLTranslationException {
    	throw new SLTranslationException("OCL Parser Error (PropertyResolver): " + message);
    }
    
    
    public boolean needVarDeclaration(String propertyName) {
        return (propertyName.equals("forAll") 
         || propertyName.equals("exists") 
         || propertyName.equals("select")
         || propertyName.equals("reject")
         || propertyName.equals("collect")
         || propertyName.equals("isUnique"));
    }


    public boolean canHandleReceiver(SLExpression receiver) {
        return true;
    }


    protected SLExpression doResolving(SLExpression receiver,
                                       String name,
                                       SLParameters parameters)
                                   throws SLTranslationException {

        OCLParameters oclParameters = null;
        
        if (parameters instanceof OCLParameters) {
            oclParameters = (OCLParameters) parameters;
        }
        
        //allInstances---------------------------------------------------------
        if(name.equals("allInstances")) {
            if(!receiver.isType() 
               || oclParameters == null
               || !oclParameters.getDeclaredVars().isEmpty()
               || !oclParameters.getEntities().isEmpty()) {
                return null;
            }

            return new OCLExpression(new OCLCollection(receiver.getKeYJavaType(javaInfo).getSort(), services));
        }
        
        
        //quantifiers----------------------------------------------------------
        if(name.equals("forAll") || name.equals("exists")) {
            if(!receiver.isCollection() 
               || oclParameters == null
               || oclParameters.getDeclaredVars().isEmpty()
               || oclParameters.getEntities().size() != 1) {
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
                    = oclParameters.getDeclaredVars().iterator();
            while(it.hasNext()) {
                Term t = replaceVar(((OCLCollection) receiver.getCollection()).getPredVar(),
                                    it.next(),
                                    ((OCLCollection) receiver.getCollection()).getPredicativeRestriction());
                restrictions = tf.createJunctorTermAndSimplify(Op.AND,
                                                               restrictions,
                                                               t);
            }
            
            Term subTerm 
                = tf.createJunctorTermAndSimplify(j,
                                                  restrictions,
                                                  oclParameters.getEntities().head().getTerm());
            Term resTerm = createdFactory.createCreatedOrNullQuantifierTerm(
                            services,
                            q,
                            oclParameters.getDeclaredVars().toArray(),
                            subTerm);

            return new OCLExpression(resTerm);
        }
        
        
        //select/reject--------------------------------------------------------
        if(name.equals("select") || name.equals("reject")) {
            if(!receiver.isCollection() 
               || oclParameters == null
               || oclParameters.getDeclaredVars().size() != 1
               || oclParameters.getEntities().size() != 1) {
                return null;
            }

            //Replace all occurrences of the new selectorVar with the 
            //appropriate collectionVar
            Term selectTerm = replaceVar(oclParameters.getDeclaredVars().head(), 
                                         ((OCLCollection) receiver.getCollection()).getPredVar(),
                                         oclParameters.getEntities().head().getTerm());
            

            if (name.equals("reject")) {
                selectTerm = tf.createJunctorTerm(Op.NOT,selectTerm);
            }
            
            LogicVariable selectVar = ((OCLCollection) receiver.getCollection()).getPredVar();
            
            OCLCollection resCollection;
            resCollection = ((OCLCollection) receiver.getCollection()).select(selectVar, selectTerm);
            
            return new OCLExpression(resCollection);            
        }
        
        
        //collect--------------------------------------------------------------
        if(name.equals("collect")) {
            if(!receiver.isCollection()
               || oclParameters == null
               || oclParameters.getDeclaredVars().size() > 1
               || oclParameters.getEntities().size() != 1) {
                return null;
            }
            
            Term collectTerm = oclParameters.getEntities().head().getTerm();
            
            if (collectTerm==null) {
                // collectTerm was a collection
                raiseError("Automatic flattening only supported for navigation over associations!");

                // System.out.println(parameters.getEntities().head().getCollection());
                //OCLCollection result = ((OCLCollection) receiver.getCollection()).collect(services,
                //              parameters.getEntities().head().getCollection());
                //return new OCLEntity(result);
                
            }
            
            if(!oclParameters.getDeclaredVars().isEmpty()) {
                collectTerm = replaceVar(oclParameters.getDeclaredVars().head(),
                                         ((OCLCollection) receiver.getCollection()).getPredVar(),
                                         collectTerm);
            }

            OCLCollection result
                = ((OCLCollection) receiver.getCollection()).collect(services, collectTerm);
            
            return new OCLExpression(result);
        } 
        
        
        //includes/excludes----------------------------------------------------
        if(name.equals("includes") || name.equals("excludes")) {
            if(!receiver.isCollection()
               || oclParameters == null
               || !oclParameters.getDeclaredVars().isEmpty()
               || oclParameters.getEntities().size() != 1) {
                return null;
            }
            
            Term opTerm 
                = tf.createEqualityTerm(((OCLCollection) receiver.getCollection()).getPredVarAsTerm(),
                                        oclParameters.getEntities().head().getTerm());
            
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
                            ((OCLCollection) receiver.getCollection()).getPredicativeRestriction(),
                            opTerm);
            
            LogicVariable[] vars = {((OCLCollection) receiver.getCollection()).getPredVar()};
            Term resTerm = createdFactory.createCreatedNotNullQuantifierTerm(
                            services,
                            q,
                            vars,
                            opTerm);
            
            return new OCLExpression(resTerm);
        }
        
        
        //isEmpty/notEmpty-----------------------------------------------------
        if(name.equals("isEmpty") || name.equals("notEmpty")) {
            if(!receiver.isCollection()
               || oclParameters == null
               || !oclParameters.getDeclaredVars().isEmpty()
               || !oclParameters.getEntities().isEmpty()) {
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
                            ((OCLCollection) receiver.getCollection()).getPredicativeRestriction(),
                            opTerm);
            
            LogicVariable[] vars = {((OCLCollection) receiver.getCollection()).getPredVar()};
            Term resTerm = createdFactory.createCreatedNotNullQuantifierTerm(
                            services,
                            q,
                            vars,
                            opTerm);
            
            return new OCLExpression(resTerm);
        }
        

        //isUnique-------------------------------------------------------------
        if(name.equals("isUnique")) {
            if(!receiver.isCollection() 
               || oclParameters == null
               || oclParameters.getDeclaredVars().size() != 1
               || oclParameters.getEntities().size() != 1) {
                return null;
            }
                        
            Term restrictions = trueTerm;
            LogicVariable temp = oclParameters.getDeclaredVars().head();
            LogicVariable lv1 
                    = new LogicVariable(new Name(temp.name()+"_1"),temp.sort());    
            LogicVariable lv2 
                    = new LogicVariable(new Name(temp.name()+"_2"),temp.sort());
            
            Term t1 = replaceVar(((OCLCollection) receiver.getCollection()).getPredVar(),
                                 lv1,
                                 ((OCLCollection) receiver.getCollection()).getPredicativeRestriction());
            Term t2 = replaceVar(((OCLCollection) receiver.getCollection()).getPredVar(),
                                 lv2,
                                 ((OCLCollection) receiver.getCollection()).getPredicativeRestriction());

            restrictions = tf.createJunctorTermAndSimplify(Op.AND,
                    t1,
                    t2);

            t1 = replaceVar(temp,
                            lv1,
                            oclParameters.getEntities().head().getTerm());
            t2 = replaceVar(temp,
                            lv2,
                            oclParameters.getEntities().head().getTerm());

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
            
            return new OCLExpression(resTerm);

        }


        //size/sum/count--------------------------------------------------------------
        if(name.equals("size") ||
           name.equals("sum")  ||
           name.equals("count")) {
            
            if(!receiver.isCollection()
               || oclParameters == null
               || oclParameters.getDeclaredVars().size() > 0
               || oclParameters.getEntities().size() != 0) {
                return null;
            }

            CollectionSort ssort = FunctionFactory.getCollectionSort(
                    receiver.getKeYJavaType(javaInfo).getSort(),
                    ((OCLCollection) receiver.getCollection()).getCollectionType());
            
            assert ssort!=null;
            
            Function f = (Function) services.getNamespaces().functions().lookup(
                    new Name(ssort.name().toString()+"::"+name));  
            
            return new OCLExpression(
                    tf.createFunctionTerm(
                            f,
                            ((OCLCollection) receiver.getCollection()).getFunctionalRestriction()));
        } 
                        

        //oclIsKindOf------------------------------------------------------------
        if(name.equals("oclIsKindOf")) {
            if(!receiver.isTerm() 
               || oclParameters == null
               || !oclParameters.getDeclaredVars().isEmpty()
               || !(oclParameters.getEntities().size() == 1)
               || !(oclParameters.getEntities().head().isType())) {
                return null;
            }
            
            Function instance = (Function) services.getNamespaces().functions().lookup(
                    new Name(oclParameters.getEntities().head().getType().getFullName()+"::instance"));
            
            Term result = tf.createFunctionTerm(instance,receiver.getTerm());
            
            return new OCLExpression(result);
        }

        
        //oclIsTypeOf------------------------------------------------------------
        if(name.equals("oclIsTypeOf")) {
            if(!receiver.isTerm() 
               || oclParameters == null
               || !oclParameters.getDeclaredVars().isEmpty()
               || !(oclParameters.getEntities().size() == 1)
               || !(oclParameters.getEntities().head().isType())) {
                return null;
            }
            
            Function instance = (Function) services.getNamespaces().functions().lookup(
                    new Name(oclParameters.getEntities().head().getType().getFullName()+"::exactInstance"));
            
            Term result = tf.createFunctionTerm(instance,receiver.getTerm());
            
            return new OCLExpression(result);
        }

        
        //oclAsType------------------------------------------------------------
        if(name.equals("oclAsType")) {
            if(!receiver.isTerm() 
               || oclParameters == null
               || !oclParameters.getDeclaredVars().isEmpty()
               || !(oclParameters.getEntities().size() == 1)
               || !(oclParameters.getEntities().head().isType())) {
                return null;
            }
            
            Term result = tf.createCastTerm(
                    (AbstractSort)oclParameters.getEntities().head().getSort(),
                    receiver.getTerm());
            
            return new OCLExpression(result);
        }

        
        //get (array access)------------------------------------------------------------
        if(name.equals("get")) {
            if(!receiver.isTerm() 
               || oclParameters == null
               || !oclParameters.getDeclaredVars().isEmpty()
               || !(oclParameters.getEntities().size() == 1)
               //|| !parameters.getEntities().head().getTerm().sort().name().toString().equals("int")
               //|| !(receiver.getSort() instanceof ArraySort)#
               ) {
                return null;
            }
            
            Term res = tf.createArrayTerm(
                    ArrayOp.getArrayOp(receiver.getKeYJavaType(javaInfo).getSort()),
                    receiver.getTerm(),
                    oclParameters.getEntities().head().getTerm());
            
            return new OCLExpression(res);
        }
        
        //signals (exception-handling)--------------------------------------------------
        if(name.equals("signals")) {
            if(oclParameters == null
               || !oclParameters.getDeclaredVars().isEmpty()
               || !(oclParameters.getEntities().size() == 1)
               || !oclParameters.getEntities().head().isType()
            ) {
                return null;
            }
            
            Sort excSort = oclParameters.getEntities().head().getType().getSort();
            Function instance = (Function) services.getNamespaces().functions().lookup(
                    new Name(excSort.name().toString()+"::instance"));  
            
            Term res = tb.and(
                        tb.not(tb.equals(tb.var(excVar),tb.NULL(services))),
                        tb.equals(tb.func(instance,tb.var(excVar)),tb.TRUE(services)));
            
            return new OCLExpression(res);
            
        }
        
        // modulo operation
        if (name.equals("mod")) {
            final IntegerLDT integerLDT = services.getTypeConverter().
                            getIntegerLDT();
            final Sort integerSort = integerLDT.targetSort();           
            if (!receiver.isTerm() 
                   || oclParameters == null 
                   || !(oclParameters.getEntities().size() == 1) 
                   || !(receiver.getKeYJavaType(javaInfo).getSort().extendsTrans(integerSort)) 
                   || !(oclParameters.getEntities().head().getSort().extendsTrans(integerSort))) {                            
                return null;
            }
            return new OCLExpression(tb.func(integerLDT.getMod(), 
                    receiver.getTerm(), 
                    oclParameters.getEntities().head().getTerm()));
        }

        // div operation
        if (name.equals("div")) {
            final IntegerLDT integerLDT = services.getTypeConverter().
                            getIntegerLDT();
            final Sort integerSort = integerLDT.targetSort();           
            if (!receiver.isTerm() 
                   || oclParameters == null 
                   || !(oclParameters.getEntities().size() == 1) 
                   || !(receiver.getKeYJavaType(javaInfo).getSort().extendsTrans(integerSort)) 
                   || !(oclParameters.getEntities().head().getSort().extendsTrans(integerSort))) {                            
                return null;
            }
            return new OCLExpression(tb.func(integerLDT.getDiv(), 
                    receiver.getTerm(), 
                    oclParameters.getEntities().head().getTerm()));
        }

/*
 * TODO
 * 
        //asSet------------------------------------------------------------
        if(name.equals("asSet")) {
            if(!receiver.isCollection()) {
                return null;
            }
            
            return new OCLEntity(((OCLCollection) receiver.getCollection()).asSet());
        }


        //asBag------------------------------------------------------------
        if(name.equals("asBag")) {
            if(!receiver.isCollection()) {
                return null;
            }
            
            return new OCLEntity(((OCLCollection) receiver.getCollection()).asBag());
        }

        
        //asSequence------------------------------------------------------------
        if(name.equals("asSequence")) {
            if(!receiver.isCollection()) {
                return null;
            }
            
            return new OCLEntity(((OCLCollection) receiver.getCollection()).asSequence());
        }
*/
        
        return null;
    }    
}
