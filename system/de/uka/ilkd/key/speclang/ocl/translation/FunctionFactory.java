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

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.CreatedAttributeTermFactory;
import de.uka.ilkd.key.speclang.translation.AxiomCollector;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

/**
 * ATTENTION: This is not a real factory in the sense of the design 
 * pattern "Factory"!
 * 
 * 
 * This Class creates all necessary functions (for the 
 * ocl-translation).
 * It also creates axioms, defining the semantics of the created functions
 * and puts them into the AxiomCollector.
 * 
 * Don't forget to reset (resetFactory) the factory for initialization!
 * 
 */
class FunctionFactory {

    public static final FunctionFactory INSTANCE = new FunctionFactory();
    
    private static final TermBuilder tb = TermBuilder.DF;
    
    private static final CreatedAttributeTermFactory createdFactory
    = CreatedAttributeTermFactory.INSTANCE;

    private Namespace functionNS;
    
    private Services services = null;

    private int axiomVarCounter = 0;
    private static final String axiomVarPrefix = "_oclAV";
    private ImmutableSet<LogicVariable> createdVars;
    
	private Namespace functions;
    
	private AxiomCollector axiomCollector;
	
    private FunctionFactory() {}

    /**
     * initialises the required parameters for the FunctionFactory to work properly
     * <b>ATTENTION:</b> must be called once before any of the other non-static methods.
     * Sets all parameters to initial values - any prior changes get lost!
     * 
     * @param services
     * @param ac
     */
    public void resetFactory(Services services, AxiomCollector ac) {
        assert services!=null;
        this.services = services;
        this.functions = services.getNamespaces().functions();
        this.axiomVarCounter = 0;
        this.createdVars = DefaultImmutableSet.<LogicVariable>nil();
        this.functionNS = new Namespace();
        this.axiomCollector = ac;
    }

    
    /**
     * 
     * creates an appropriate function-symbol representing allInstances of the given sort
     * and the axiom that specifies the meaning of this function-symbol
     * 
     * C.allInstances()
     * 
     * @param csort CollectionSort of the function-symbol 
     */
    public Function createAllInstancesConstant(CollectionSort csort)
    {
        
        // lookup function
        Function allInst = (Function) functionNS.lookup(new Name(csort.elementSort().name().toString()+"::allInstances"));
        if(allInst!=null) {
            return allInst;
        }
        
        // create function-Symbol
        allInst = new NonRigidFunction(
                new Name(csort.elementSort().name().toString()+"::allInstances"),
                csort,
                new Sort[] {});
        
        this.functionNS.add(allInst);
        
        // create axiom
        Function isIn = (Function) this.functions.lookup(new Name(csort.name().toString()+"::includes"));
        LogicVariable v = createVar(csort.elementSort());
        
        Term subTerm = tb.func(isIn,tb.func(allInst),tb.var(v));
        Term axiom = createdFactory.createCreatedNotNullQuantifierTerm(
                services,
                Op.ALL,
                v,
                subTerm);

        axiomCollector.collectAxiom(allInst, axiom);
        
        Function instOf = (Function) this.functions.lookup(new Name(csort.elementSort().name().toString()+"::instance"));
        
        LogicVariable jObject = createVar(services.getJavaInfo().getJavaLangObjectAsSort());
        
        subTerm = tb.imp(
        		tb.func(isIn,
        				tb.func(allInst),
        					tb.tf().createCastTerm(((AbstractSort)csort.elementSort()),tb.var(jObject))),
        		tb.equals(
        				tb.func(instOf,tb.var(jObject)),
        				tb.TRUE(services)));
        
        axiom = createdFactory.createCreatedNotNullQuantifierTerm(
        		services,
        		Op.ALL,
        		jObject,
        		subTerm);
        
        axiomCollector.collectAxiom(allInst, axiom);
        
        return allInst;
    }
    
    
    /**
     * 
     * creates an appropriate function-symbol representing allInstances of the given sort
     * and the axiom that specifies the meaning of this function-symbol
     * 
     * @param sort Element-Sort of the function-symbol
     */
    public Function createAllInstancesConstant(Sort sort) {
        return createAllInstancesConstant(getSetSort(sort));
    }
    
    
    /**
     * 
     * creates an appropriate function-symbol representing select for the given term
     * and adds the axioms that specifie the meaning of this function-symbol to the
     * local axiom-list
     * 
     * c->select(e | b)
     * 
     * @param selectVar Translation of e
     * @param selectTerm Translation of b 
     * @throws SLTranslationException 
     */
    public Function createSelectFunction(LogicVariable selectVar,
            Term selectTerm,
            int collectionType) throws SLTranslationException
    {
        CollectionSort csort = getCollectionSort(selectVar.sort(),collectionType);
        assert csort!=null;
        
        // lookup function
        Function f = (Function) functionNS.lookup(new Name(csort.elementSort().toString()+"::select["+selectTerm.toString()+"]"));
//        Function f = (Function) functionNS.lookup(new Name(csort.elementSort().toString()+"::select"));
        if(f!=null) {
            return f;
        }
        
        ImmutableSet<QuantifiableVariable> vars = selectTerm.freeVars();
        // selectVar is NOT free in this sense.
        vars = vars.remove(selectVar);
        
        Sort[] sorts = new Sort[vars.size()+1];
        Term[] varTerms1 = new Term[vars.size()+1];
        Term[] varTerms2 = new Term[vars.size()+1];
        LogicVariable[] qvars1 = new LogicVariable[vars.size()];
        LogicVariable[] qvars2 = new LogicVariable[vars.size()+2];
        
        int i=0;
        for(QuantifiableVariable qvar : vars) {            
            final LogicVariable var = (LogicVariable)qvar;
            sorts[i+1] = var.sort();
            varTerms1[i+1] = (varTerms2[i+1] = tb.var(var));
            qvars1[i] = var;
            qvars2[i+2] = var;
            i++;
        }
        
        sorts[0] = csort;
        
        //create new function-symbol
        Function selectE = new RigidFunction( new Name(csort.elementSort().toString()+"::select["+selectTerm.toString()+"]"),
//        Function selectE = new RigidFunction( new Name(csort.elementSort().toString()+"::select"),
                csort,
                sorts);
        
        functionNS.add(selectE);

        // create axioms
        Function emptyCollection = getEmptyCollection(csort.elementSort(),collectionType);

        // axiom 1
        varTerms1[0] = tb.func(emptyCollection);
        Term axiom1 = tb.equals(
                tb.func(selectE,varTerms1),
                tb.func(emptyCollection));
        
        if(qvars1.length>0) {
            axiom1 = createdFactory.createCreatedNotNullQuantifierTerm(services,Op.ALL,qvars1,axiom1);
        }

        axiomCollector.collectAxiom(selectE, axiom1);
        
        // axiom 2
        qvars2[0] = createVar(csort);
        qvars2[1] = createVar(csort.elementSort());
        
        varTerms1[0] = including(
                tb.var(qvars2[0]),
                tb.var(qvars2[1]));
        
        varTerms2[0] = tb.var(qvars2[0]);
        
        Term axiom2 = tb.imp(
                replaceVar(selectVar,qvars2[1],selectTerm),
                tb.equals(
                        tb.func(selectE,varTerms1),
                        including(
                                tb.func(selectE,varTerms2),
                                tb.var(qvars2[1]))));
        
        axiom2 = createdFactory.createCreatedNotNullQuantifierTerm(services,Op.ALL,qvars2,axiom2);
        
        axiomCollector.collectAxiom(selectE, axiom2);

        // axiom 3
        Term axiom3 = tb.imp(
                tb.not(replaceVar(selectVar,qvars2[1],selectTerm)),
                tb.equals(
                        tb.func(selectE,varTerms1),
                        tb.func(selectE,varTerms2)));
        
        axiom3 = createdFactory.createCreatedNotNullQuantifierTerm(services,Op.ALL,qvars2,axiom3);
        
        axiomCollector.collectAxiom(selectE, axiom3);

        return selectE;
    }

    
    /**
     * 
     * creates an appropriate function-symbol representing reject for the given term
     * and adds the axioms that specifie the meaning of this function-symbol to the
     * local axiom-list
     * 
     * c->reject(e | b)
     * 
     * @param rejectVar Translation of e
     * @param rejectTerm Translation of b 
     * @throws SLTranslationException 
     */
    public Function createRejectFunction(LogicVariable rejectVar,
            Term rejectTerm,
            int collectionType) throws SLTranslationException
    {
        return createSelectFunction(rejectVar,
                tb.not(rejectTerm),
                collectionType);
    }

    
    /**
     * 
     * creates an appropriate function-symbol representing collect for the given term
     * and adds the axioms that specify the meaning of this function-symbol to the
     * local axiom-list
     * 
     * c->collect(e | b)
     * 
     * @param collectVar Translation of e
     * @param collectTerm Translation of b 
     * @throws SLTranslationException 
     */
    public Function createCollectFunction(LogicVariable collectVar,
            Term collectTerm,
            int collectionType) throws SLTranslationException
    {
        
        CollectionSort csort = getCollectionSort(collectVar.sort(),collectionType);

        CollectionSort resSort =
            (collectionType == OCLCollection.OCL_SET) ?
                    getBagSort(collectTerm.sort()) :
                        getCollectionSort(collectTerm.sort(),collectionType);
        
        // lookup function
        Function f = (Function) functionNS.lookup(new Name(csort.elementSort().toString()+"::collect"));
        if(f!=null) {
            return f;
        }
        
        ImmutableSet<QuantifiableVariable> vars = collectTerm.freeVars();
        
        // collectVar is NOT free in collectTerm in this sense
        vars = vars.remove(collectVar);
        
        Sort[] signature = new Sort[vars.size()+1];
        Term[] varTerms1 = new Term[vars.size()+1];
        Term[] varTerms2 = new Term[vars.size()+1];
        LogicVariable[] qvars1 = new LogicVariable[vars.size()];
        LogicVariable[] qvars2 = new LogicVariable[vars.size()+2];
        
        int i=0;
        for(QuantifiableVariable qvar : vars) {            
            final LogicVariable var = (LogicVariable)qvar;
            signature[i+1] = var.sort();
            varTerms1[i+1] = (varTerms2[i+1] = tb.var(var));
            qvars1[i] = var;
            qvars2[i+2] = var;
        }
        
        signature[0] = csort;
        
        //create new function-symbol
        Function collectE = new RigidFunction( new Name(csort.elementSort().toString()+"::collect"),
                resSort,
                signature);
        
        functionNS.add(collectE);

        // create axioms
        // axiom 1
        Function emptyCollectionT = getEmptyCollection(csort.elementSort(),collectionType);
        assert emptyCollectionT != null;
        
        Function emptyCollectionS = (collectionType == OCLCollection.OCL_SET) ?
                getEmptyBag(collectTerm.sort()) :
                    getEmptyCollection(collectTerm.sort(),collectionType);        
        assert emptyCollectionS != null;
        
        varTerms1[0] = tb.func(emptyCollectionT);
        Term axiom1 = tb.equals(
                tb.func(collectE,varTerms1),
                tb.func(emptyCollectionS));
        
        if(qvars1.length>0) {
            axiom1 = createdFactory.createCreatedNotNullQuantifierTerm(services,Op.ALL,qvars1,axiom1);
        }

        axiomCollector.collectAxiom(collectE, axiom1);
        
        //System.out.println("Creating axiom2");
        // axiom 2
        qvars2[0] = createVar(csort);
        qvars2[1] = createVar(csort.elementSort());
        
        varTerms1[0] = including(
                tb.var(qvars2[0]),
                tb.var(qvars2[1]));
        
        varTerms2[0] = (collectionType == OCLCollection.OCL_SET) ?
                excluding(
                        tb.var(qvars2[0]),
                        tb.var(qvars2[1])) :
                tb.var(qvars2[0]);
        
        Term eq2 = null;

       	if (collectTerm.sort() instanceof AbstractNonCollectionSort) {
        	eq2 = including(
        			tb.func(collectE,varTerms2),
                    replaceVar(collectVar,qvars2[1],collectTerm));
        } else if (collectTerm.sort() instanceof AbstractCollectionSort) {
        	//System.out.println("Building union");
        	eq2 = union(
        			tb.func(collectE,varTerms2),
                    replaceVar(collectVar,qvars2[1],collectTerm));
        	//System.out.println("union-term: " + eq2);
        } else {
        	raiseError("wrong sort in collectTerm!");
        }
        
       	//System.out.println("axiom2");
        Term axiom2 = tb.equals(
                        tb.func(collectE,varTerms1),
                        eq2);
        
        axiom2 = createdFactory.createCreatedNotNullQuantifierTerm(services,Op.ALL,qvars2,axiom2);
        
        axiomCollector.collectAxiom(collectE, axiom2);

        //System.out.println("Returning from Collect-Creation");
        return collectE;
    }

    
    private void raiseError(String msg) throws SLTranslationException {
		throw new SLTranslationException("Error while generating Functions: " + msg, "no file", Position.UNDEFINED);
	}

	private Term replaceVar(LogicVariable lv1, LogicVariable lv2, Term term) {
        Map<LogicVariable, LogicVariable> map = 
            new LinkedHashMap<LogicVariable, LogicVariable>();
        map.put(lv1, lv2);
        OpReplacer or = new OpReplacer(map);
        return or.replace(term);
    }

    
    /**
     * 
     * @return Conjunction of subTerms
     */
    public static Term buildAddTerm(Term[] subTerms) {
        Term result = tb.tt();
        for (Term subTerm : subTerms) {
            result = tb.and(result, subTerm);
        }
        
        return result;
    }
        
    
    /**
     * Returns the corresponding CollectionSort of the given sort
     * @param sort
     * @param collectionType the concrete collection type according to OCLCollection
     * @return <b>null</b> if no AbstractNonCollectionSort is given,
     * otherwise the corresponding CollectionSort is returned.
     */
    public static CollectionSort getCollectionSort(Sort sort, int collectionType)
    {
        CollectionSort ssort = null;
        
        if(sort instanceof AbstractNonCollectionSort) {
            switch(collectionType) {
                case OCLCollection.OCL_SET :
                    ssort = ((AbstractNonCollectionSort) sort).getSetSort();
                    break;
                case OCLCollection.OCL_BAG :
                    ssort = ((AbstractNonCollectionSort) sort).getBagSort();
                    break;
                case OCLCollection.OCL_SEQUENCE :
                    ssort = ((AbstractNonCollectionSort) sort).getSequenceSort();
                    break;
            }
        } else if (sort instanceof AbstractCollectionSort) {
            switch(collectionType) {
            	case OCLCollection.OCL_SET :
            		ssort = ((AbstractNonCollectionSort)((AbstractCollectionSort) sort).elementSort()).getSetSort();
            		break;
            	case OCLCollection.OCL_BAG :
            		ssort = ((AbstractNonCollectionSort)((AbstractCollectionSort) sort).elementSort()).getBagSort();
            		break;
            	case OCLCollection.OCL_SEQUENCE :
            		ssort = ((AbstractNonCollectionSort)((AbstractCollectionSort) sort).elementSort()).getSequenceSort();
            		break;
            }
        }

        return ssort;
    }

    
    public static CollectionSort getSetSort(Sort sort) {
        return getCollectionSort(sort, OCLCollection.OCL_SET);
    }
    
    
    public static CollectionSort getBagSort(Sort sort) {
        return getCollectionSort(sort, OCLCollection.OCL_BAG);
    }

    
    public static CollectionSort getSequenceSort(Sort sort) {
        return getCollectionSort(sort, OCLCollection.OCL_SEQUENCE);
    }

    
    /**
     * Returns the function-symbol representing emptyCollection of the given type and sort
     * 
     * @param sort of the collection
     * @return function-symbol representing emptyCollection
     */
    public Function getEmptyCollection(Sort sort, int collectionType) {
        
        CollectionSort ssort = getCollectionSort(sort, collectionType);

        String functionName = null;
        
        switch(collectionType) {
            case OCLCollection.OCL_SET : functionName="::emptySet";
                break;
            case OCLCollection.OCL_BAG : functionName="::emptyBag";
                break;
            case OCLCollection.OCL_SEQUENCE : functionName="::emptySequence";
                break;
        }
                
        Function f = (Function) this.functions.lookup(
                new Name(ssort.name().toString()+functionName));
        
        return f;
    }

    
    /**
     * Returns the function-symbol representing emptySet of the given sort
     * 
     * @param sort may be the elementsort or the collectionsort
     * @return function-symbol representing emptySet
     */
    public Function getEmptySet(Sort sort) {
        return getEmptyCollection(sort,OCLCollection.OCL_SET);
    }

    
    /**
     * Returns the function-symbol representing emptyBag of the given sort
     * 
     * @param sort may be the elementsort or the collectionsort
     * @return function-symbol representing emptyBag
     */
    public Function getEmptyBag(Sort sort) {
        return getEmptyCollection(sort,OCLCollection.OCL_BAG);
    }

    
    /**
     * Returns the function-symbol representing emptySequence of the given sort
     * 
     * @param sort may be the elementsort or the collectionsort
     * @return function-symbol representing emptySequence
     */
    public Function getEmptySequence(Sort sort) {
        return getEmptyCollection(sort,OCLCollection.OCL_SEQUENCE);
    }

    
    public Term including(Term setSymbol, Term element) throws SLTranslationException {
        
        if( !(setSymbol.sort() instanceof AbstractCollectionSort) ||
            !(element.sort().extendsTrans( ((AbstractCollectionSort)setSymbol.sort()).elementSort() )) ) {
            
            raiseError("including failed since the terms used have wrong sorts\n" +
                    "Sorts were: " + setSymbol.sort() + " " + element.sort());
        }
        
        Function inc = (Function) this.functions.lookup(new Name(setSymbol.sort().name().toString()+"::including"));
        
        return tb.func(inc,setSymbol,element);
    }

    public Term excluding(Term setSymbol, Term element) throws SLTranslationException {
        
        if( !(setSymbol.sort() instanceof AbstractCollectionSort) ||
            !(element.sort().extendsTrans( ((AbstractCollectionSort)setSymbol.sort()).elementSort() )) ) {
            
            raiseError("including failed since the terms used have wrong sorts\n" +
                    "Sorts were: " + setSymbol.sort() + " " + element.sort());
        }
        
        Function inc = (Function) this.functions.lookup(new Name(setSymbol.sort().name().toString()+"::excluding"));
        
        return tb.func(inc,setSymbol,element);
    }

    public Term union(Term t1, Term t2) throws SLTranslationException {
        
        if( !(t1.sort() instanceof AbstractCollectionSort) ||
            !(t2.sort() instanceof AbstractCollectionSort))
        {
            raiseError("no collection-sorts in union" +
                    "Sorts were: " + t1.sort() + " " + t2.sort());
        }
        
        Sort s = null;
        if(((AbstractCollectionSort) t1.sort()).elementSort().extendsTrans(
                ((AbstractCollectionSort) t2.sort()).elementSort())) {
            s = t2.sort();
        } else if (((AbstractCollectionSort) t2.sort()).elementSort().extendsTrans(
                ((AbstractCollectionSort) t1.sort()).elementSort())) {
            s = t1.sort();
        } else {
            raiseError("union failed since the terms used have diffrent sorts\n" +
                    "Sorts were: " + t1.sort() + " " + t2.sort());
        }
        assert s != null;
        
        final Function union = (Function) 
           this.functions.lookup(new Name(s.name().toString()+"::union"));
        
        return tb.func(union,t1,t2);
    }

    public Term simplify(Term t) {
    
    	Term result = t;
    	
        if (t.op().name().toString().indexOf("::union") != -1) {
            if(t.sub(1).op().name().toString().indexOf("::including") != -1) {
                if(t.sub(1).sub(0).op().name().toString().indexOf("::emptySet") != -1) {
                    result = tb.func((Function)t.sub(1).op(),t.sub(0),t.sub(1).sub(1));
                }
            }
            else if(t.sub(0).op().name().toString().indexOf("::including") != -1) {
                if(t.sub(0).sub(0).op().name().toString().indexOf("::emptySet") != -1) {
                    result = tb.func((Function)t.sub(0).op(),t.sub(1),t.sub(0).sub(1));
                }
            }
        }
        
        return result;
    }
    

    public Term createRangedSet(Term lowerBound, Term upperBound, Function leq) throws SLTranslationException {

        if(lowerBound.sort()!=upperBound.sort()) {
            raiseError("Set{"+lowerBound.toString()+".."+upperBound.toString()+"} : sorts don't match");
        }
        
        ImmutableSet<QuantifiableVariable> vars = lowerBound.freeVars().union(upperBound.freeVars());
        
        Sort[] sorts = new Sort[vars.size()];
        Term[] varTerms = new Term[vars.size()];
        LogicVariable[] qvars = new LogicVariable[vars.size()+1];
        
        int i=0;
        for(QuantifiableVariable qvar : vars) {
            LogicVariable var = (LogicVariable) qvar;
            sorts[i] = var.sort();
            varTerms[i] = tb.var(var);
            qvars[i+1] = var;
            i++;
        }
        
        //create new function
        Function setE = new RigidFunction( new Name("set::["+lowerBound.toString()+".."+upperBound.toString()+"]"),
                getSetSort(lowerBound.sort()),
                sorts);
        
        functionNS.add(setE);
        
        //create axiom
        LogicVariable v = createVar(lowerBound.sort());
        qvars[0] = v;

        Term axiom1 = createRangedCollectionAxiom1(
                lowerBound,
                upperBound,
                setE,
                leq,
                varTerms,
                qvars);
        
        axiomCollector.collectAxiom(setE, axiom1);

        return tb.func(setE,varTerms);
    }

    

    public Term createRangedBag(Term lowerBound, Term upperBound, Function leq) throws SLTranslationException {

        if(lowerBound.sort()!=upperBound.sort()) {
            raiseError("Bag{"+lowerBound.toString()+".."+upperBound.toString()+"} : sorts don't match");
        }
        
        ImmutableSet<QuantifiableVariable> vars = lowerBound.freeVars().union(upperBound.freeVars());
        
        Sort[] sorts = new Sort[vars.size()];
        Term[] varTerms = new Term[vars.size()];
        LogicVariable[] qvars = new LogicVariable[vars.size()+1];
        
        int i=0;
        for(QuantifiableVariable qvar : vars) {
            LogicVariable var = (LogicVariable) qvar;
            sorts[i] = var.sort();
            varTerms[i] = tb.var(var);
            qvars[i+1] = var;
            i++;
        }
        
        //create new function
        Function bagE = new RigidFunction( new Name("bag::["+lowerBound.toString()+".."+upperBound.toString()+"]"),
                getBagSort(lowerBound.sort()),
                sorts);
        
        functionNS.add(bagE);
        
        //create axiom 1
        LogicVariable v = createVar(lowerBound.sort());
        qvars[0] = v;

        Term axiom1 = createRangedCollectionAxiom1(
                lowerBound,
                upperBound,
                bagE,
                leq,
                varTerms,
                qvars);
        
        axiomCollector.collectAxiom(bagE, axiom1);

        // create axiom 2
        Term axiom2 = createRangedCollectionAxiom2(
                bagE,
                leq,
                varTerms,
                qvars);
        
        axiomCollector.collectAxiom(bagE, axiom2);
        
        return tb.func(bagE,varTerms);
    }

    
    public Term createRangedSequence(Term lowerBound, Term upperBound, Function leq) throws SLTranslationException {

        if(lowerBound.sort()!=upperBound.sort()) {
            raiseError("Sequence{"+lowerBound.toString()+".."+upperBound.toString()+"} : sorts don't match");
        }
        
        ImmutableSet<QuantifiableVariable> vars = lowerBound.freeVars().union(upperBound.freeVars());
        
        Sort[] sorts = new Sort[vars.size()];
        Term[] varTerms = new Term[vars.size()];
        LogicVariable[] qvars = new LogicVariable[vars.size()+1];
        LogicVariable[] qvars2 = new LogicVariable[vars.size()+2];
        
        int i=0;
        for(QuantifiableVariable qvar : vars) {
            LogicVariable var = (LogicVariable) qvar;
            sorts[i] = var.sort();
            varTerms[i] = tb.var(var);
            qvars[i+1] = var;
            qvars2[i+2] = var;
            i++;
        }
        
        //create new function
        Function sequenceE = new RigidFunction( new Name("sequence::["+lowerBound.toString()+".."+upperBound.toString()+"]"),
                getSequenceSort(lowerBound.sort()),
                sorts);
        
        functionNS.add(sequenceE);
        
        LogicVariable v = createVar(lowerBound.sort());
        qvars[0] = v;

        Term axiom1 = createRangedCollectionAxiom1(
                lowerBound,
                upperBound,
                sequenceE,
                leq,
                varTerms,
                qvars);
        
        axiomCollector.collectAxiom(sequenceE, axiom1);


        Term axiom2 = createRangedCollectionAxiom2(
                sequenceE,
                leq,
                varTerms,
                qvars);
        
        axiomCollector.collectAxiom(sequenceE, axiom2);
        
        // create axiom 3
        
        qvars2[0] = v;
        qvars2[1] = createVar(lowerBound.sort());
        
        Term axiom3 = createRangedCollectionAxiom3(
                sequenceE,
                leq,
                varTerms,
                qvars2);
        
        axiomCollector.collectAxiom(sequenceE, axiom3);
        
        return tb.func(sequenceE,varTerms);
    }


    private Term createRangedCollectionAxiom1(
            Term lowerBound,
            Term upperBound,
            Function funcSymbol,
            Function leq,
            Term[] varTerms,
            LogicVariable[] qvars) {
        
        Function isIn = (Function) this.functions.lookup(
                new Name(funcSymbol.sort().name()+"::includes"));
        
        Term vterm = tb.var(qvars[0]);
        
        Term subTerm = tb.and(
                tb.func(leq,new Term[] {lowerBound,vterm}),
                tb.func(leq,new Term[] {vterm,upperBound}));
        
        subTerm = tb.equals(
                tb.func(isIn,
                        tb.func(funcSymbol,varTerms),
                        vterm),
                subTerm);
        
        Term axiom = createdFactory.createCreatedNotNullQuantifierTerm(
                services,
                Op.ALL,
                qvars,
                subTerm);
        
        return axiom;
        
    }
    
    
    private Term createRangedCollectionAxiom2(
            Function funcSymbol,
            Function leq,
            Term[] varTerms,
            LogicVariable[] qvars) {
        
        Function count = (Function) this.functions.lookup(
                new Name(funcSymbol.sort().name()+"::count"));
        
        Term subTerm = tb.func(leq, 
                tb.func(count,
                    new Term[] {
                        tb.func(funcSymbol,varTerms),
                        tb.var(qvars[0])} ),
                tb.zTerm(services, "1"));
        
        Term axiom2 = createdFactory.createCreatedNotNullQuantifierTerm(
                services,
                Op.ALL,
                qvars,
                subTerm);
        
        return axiom2;
        
    }

    
    private Term createRangedCollectionAxiom3(
            Function funcSymbol,
            Function leq,
            Term[] varTerms,
            LogicVariable[] qvars) {
        
        Function at = (Function) this.functions.lookup(
                new Name(funcSymbol.sort().name()+"::at"));
        
        Term subTerm = tb.imp(
                tb.func(leq,
                        tb.var(qvars[0]),
                        tb.var(qvars[1])),
                tb.func(leq,
                        tb.func(at,
                                tb.func(funcSymbol,varTerms),
                                tb.var(qvars[0])),
                        tb.func(at,
                                tb.func(funcSymbol,varTerms),
                                tb.var(qvars[1]))));
        

        Term axiom3 = createdFactory.createCreatedNotNullQuantifierTerm(
                services,
                Op.ALL,
                qvars,
                subTerm);
        
        return axiom3;
        
    }

    
    private LogicVariable createVar(Sort sort) {
        LogicVariable v = new LogicVariable(new Name(axiomVarPrefix + axiomVarCounter++), sort);
        createdVars = createdVars.add(v);
        return v;
    }

    public Term unionAndSimplify(Term t1, Term t2) throws SLTranslationException {
        
        Term res = union(t1,t2);
        Term oldRes;
        do {
            oldRes = res;
            res = simplify(res);
        } while (!oldRes.equals(res));
        
        return res;
    }
        
    
    /**
     * returns the namespace which holds all the created functions
     */
    public Namespace getFunctions() {
        return this.functionNS;
    }


    /**
     * returns the list of created variables which are used in the axioms
     */
    public ImmutableSet<LogicVariable> getCreatedVars() {
        return this.createdVars;
    }
    
}
