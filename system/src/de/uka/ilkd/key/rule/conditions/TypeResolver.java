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


package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;


/**
 * Several variable conditions deal with types. The type resolver provides a 
 * unique interface to access types, e.g. the type of a schemavariable instantiation,
 * the instantiated type of a generic sort or the type an attribute is declared in. 
 */
public abstract class TypeResolver {
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------         
    
    public static TypeResolver createContainerTypeResolver(SchemaVariable s) {
        return new ContainerTypeResolver(s);
    }
        
    public static TypeResolver createElementTypeResolver(SchemaVariable s) {
        return new ElementTypeResolverForSV(s);
    }
    
    public static TypeResolver createGenericSortResolver(GenericSort gs) {
        return new GenericSortResolver(gs);
    }
    
    public static TypeResolver createNonGenericSortResolver(Sort s) {
	return new NonGenericSortResolver(s);
    }
    
    
    public abstract boolean isComplete(SchemaVariable sv, 
            			       SVSubstitute instCandidate, 
            			       SVInstantiations instMap, 
            			       Services services);
    
    public abstract Sort resolveSort(SchemaVariable sv, 
            			     SVSubstitute instCandidate, 
            			     SVInstantiations instMap, 
            			     Services services);
    
    
    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------     
    
    public static class GenericSortResolver extends TypeResolver {

        private final GenericSort gs;
        
        public GenericSortResolver(GenericSort gs) {          
            this.gs = gs;
        }

        public GenericSort getGenericSort(){
            return gs;
        }
        
        @Override
        public boolean isComplete(SchemaVariable sv, SVSubstitute instCandidate, 
                SVInstantiations instMap, Services services) {            
            return instMap.getGenericSortInstantiations().getInstantiation(gs) != null;
        }

        @Override
        public Sort resolveSort(SchemaVariable sv, SVSubstitute instCandidate, 
                SVInstantiations instMap, Services services) {
            return instMap.getGenericSortInstantiations().getInstantiation(gs);
        }
        
        @Override
        public String toString() {
            return gs.toString();
        }
    }
    
    public static class NonGenericSortResolver extends TypeResolver {

        private final Sort s;
        
        public NonGenericSortResolver(Sort s) {          
            this.s = s;
        }

        @Override
        public boolean isComplete(SchemaVariable sv, SVSubstitute instCandidate, 
                SVInstantiations instMap, Services services) {            
            return true;
        }

        @Override
        public Sort resolveSort(SchemaVariable sv, SVSubstitute instCandidate, 
                SVInstantiations instMap, Services services) {
            return s;
        }
        
        public Sort getSort(){
            return s;
        }
        
        @Override
        public String toString() {
            return s.toString();
        }        
    }
    
    public static class ElementTypeResolverForSV extends TypeResolver {

        private final SchemaVariable resolveSV;
        
        public ElementTypeResolverForSV(SchemaVariable sv) {
            this.resolveSV = sv;
        }
        
        @Override
        public boolean isComplete(SchemaVariable sv, SVSubstitute instCandidate, 
                SVInstantiations instMap, Services services) {       
            return resolveSV == sv || instMap.getInstantiation(resolveSV) != null;
        }

        @Override
        public Sort resolveSort(SchemaVariable sv, SVSubstitute instCandidate, 
                SVInstantiations instMap, Services services) {
            
            final Sort s;        
            
            final SVSubstitute inst = (SVSubstitute) (resolveSV == sv ? instCandidate : 
                instMap.getInstantiation(resolveSV));
            
            if (inst instanceof ProgramVariable) {
                s = ((ProgramVariable)inst).sort();
            } else {              
                Term gsTerm = null;
                if (inst instanceof Term) {
                    gsTerm = (Term) inst;
                } else if (inst instanceof ProgramElement) {
                    gsTerm = services.getTypeConverter().
                    convertToLogicElement((ProgramElement)inst, instMap.getExecutionContext());
                } else {
                    Debug.fail("Unexpected substitution for sv " + resolveSV +":" + inst);
                    return null;
                }
                s = gsTerm.sort();
            }
            return s;
        }

        @Override
        public String toString() {
            return "\\typeof(" + resolveSV  + ")";
        }
    }
   
    
    public static class ContainerTypeResolver extends TypeResolver {
                
        private final SchemaVariable memberSV;

        public ContainerTypeResolver(SchemaVariable sv) {
            this.memberSV = sv;
        }

        @Override
        public boolean isComplete(SchemaVariable sv,
                SVSubstitute instCandidate, SVInstantiations instMap,
                Services services) {
            
            return sv == memberSV || instMap.getInstantiation(memberSV) != null;
        }

        @Override
        public Sort resolveSort(SchemaVariable sv, 
        			SVSubstitute instCandidate,
        			SVInstantiations instMap, 
        			Services services) {     
            final Sort result;
            
            final SVSubstitute inst = (SVSubstitute) (memberSV == sv ? instCandidate : 
                instMap.getInstantiation(memberSV)); 

            if (inst instanceof Operator) {
                result = getContainerSort((Operator)inst, services);
            } else {
                if (inst instanceof Expression) {
                    result = getContainerSort
                    (services.getTypeConverter().convertToLogicElement((Expression)inst, 
                            instMap.getExecutionContext()).op(), services);
                } else if (inst instanceof Term) {
                    result = getContainerSort(((Term)inst).op(), services);
                } else {
                    Debug.fail("Unexpected instantiation for SV " + memberSV + ":" + inst);
                    result = null;
                }
            }     
            return result;
        }
    
        private Sort getContainerSort(Operator op, Services services) {
            Sort result = null;
            if (op instanceof ProgramVariable) {
                result  = ((ProgramVariable)op).getContainerType().getSort();
            } else if(op instanceof IObserverFunction) {
        	result = ((IObserverFunction)op).getContainerType().getSort();
            } else if(op instanceof Function
        	      && ((Function)op).isUnique()
        	      && ((Function)op).name().toString().contains("::")) {
        	//Heap
        	Function func = (Function) op;
        	String funcName = func.name().toString();
        	String sortName = funcName.substring(0, funcName.indexOf("::"));
        	return (Sort) 
        	   services.getNamespaces().sorts().lookup(new Name(sortName));
            } else {
                Debug.fail("Unknown member type", op);
            }
            return result;
        }
        
        @Override
        public String toString() {
            return "\\containerType(" + memberSV  + ")";
        }
    }
}
