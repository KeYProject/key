// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;


/**
 * Several variable conditions deal with types. The type resolver provides a 
 * unique interface to access types, e.g. the type of a schemavariable instantiation,
 * the instantiated type of a generic sort or the type an attribut eis declared in. 
 *
 */
public abstract class TypeResolver {
    
    
    public static TypeResolver createContainerTypeResolver(SchemaVariable s) {
        return new ContainerTypeResolver(s);
    }
    
    public static TypeResolver createElementTypeResolver(SchemaVariable s) {
        return new ElementTypeResolverForSV(s);
    }
    
    public static TypeResolver createGenericSortResolver(GenericSort gs) {
        return new GenericSortResolver(gs);
    }
    
    
    
    public static class GenericSortResolver extends TypeResolver {

        private final GenericSort gs;
        
        public GenericSortResolver(GenericSort gs) {          
            this.gs = gs;
        }

        public boolean isComplete(SchemaVariable sv, SVSubstitute instCandidate, 
                SVInstantiations instMap, Services services) {            
            return instMap.getGenericSortInstantiations().getInstantiation(gs) != null;
        }

        public Sort resolveSort(SchemaVariable sv, SVSubstitute instCandidate, 
                SVInstantiations instMap, Services services) {
            return instMap.getGenericSortInstantiations().getInstantiation(gs);
        }

        public KeYJavaType resolveType(SchemaVariable sv, SVSubstitute instCandidate, 
                SVInstantiations instMap, Services services) {            
            final Sort s = resolveSort(sv, instCandidate, instMap, services);
            return services.getJavaInfo().getKeYJavaType(s);
        }
        
        public String toString() {
            return gs.toString();
        }
        
        public GenericSort getGenericSort() {return gs;}
    }
    public static class ElementTypeResolverForSV extends TypeResolver {

        private final SortedSchemaVariable resolveSV;
        
        public ElementTypeResolverForSV(SchemaVariable sv) {
            if (!(sv instanceof SortedSchemaVariable)) {
                throw new IllegalArgumentException("Expected a SortedSchemaVariable," +
                                " but is "+sv);
            }
            this.resolveSV = (SortedSchemaVariable) sv;
        }
        
        public boolean isComplete(SchemaVariable sv, SVSubstitute instCandidate, 
                SVInstantiations instMap, Services services) {       
            return resolveSV == sv || instMap.getInstantiation(resolveSV) != null;
        }

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

        public KeYJavaType resolveType(SchemaVariable sv, SVSubstitute instCandidate, 
                SVInstantiations instMap, Services services) {            
            final Sort s = resolveSort(sv, instCandidate, instMap, services);
            return services.getJavaInfo().getKeYJavaType(s);
        }
       
        public String toString() {
            return "\\typeof(" + resolveSV  + ")";
        }
    }
   
    public static class ContainerTypeResolver extends TypeResolver {
                
        private final SchemaVariable memberSV;

        public ContainerTypeResolver(SchemaVariable sv) {
            this.memberSV = sv;
        }

        public boolean isComplete(SchemaVariable sv,
                SVSubstitute instCandidate, SVInstantiations instMap,
                Services services) {
            
            return sv == memberSV || instMap.getInstantiation(memberSV) != null;
        }

        public Sort resolveSort(SchemaVariable sv, SVSubstitute instCandidate,
                SVInstantiations instMap, Services services) {            
            return resolveType(sv, instCandidate, instMap, services).getSort();
        }

        public KeYJavaType resolveType(SchemaVariable sv,
                SVSubstitute instCandidate, SVInstantiations instMap,
                Services services) {
            
            final KeYJavaType resolvedType;
            
            final SVSubstitute inst = (SVSubstitute) (memberSV == sv ? instCandidate : 
                instMap.getInstantiation(memberSV)); 
            
            if (inst instanceof Operator) {
                resolvedType = getContainerType(inst);
            } else {
                if (inst instanceof Expression) {
                    resolvedType = getContainerType
                    (services.getTypeConverter().convertToLogicElement((Expression)inst, 
                            instMap.getExecutionContext()).op());
                } else if (inst instanceof Term) {
                    resolvedType = getContainerType(((Term)inst).op());
                } else {
                    Debug.fail("Unexpected instantiation for SV " + memberSV + ":" + inst);
                    resolvedType = null;
                }
            }     
            return resolvedType;
        }
    
        private KeYJavaType getContainerType(SVSubstitute inst) {
            KeYJavaType resolvedType = null;
            if (inst instanceof ProgramVariable) {
                resolvedType  = ((ProgramVariable)inst).getContainerType();
            } else if (inst instanceof AttributeOp) {
                resolvedType = ((AttributeOp)inst).getContainerType();
            } else {
                Debug.fail("Unknown member type: ", inst);
            }
            return resolvedType;
        }
        
        public String toString() {
            return "\\containerType(" + memberSV  + ")";
        }
    }
    
    public abstract boolean isComplete(SchemaVariable sv, 
            SVSubstitute instCandidate, SVInstantiations instMap, Services services);
    
    public abstract Sort resolveSort(SchemaVariable sv, 
            SVSubstitute instCandidate, SVInstantiations instMap, Services services);
    
    public abstract KeYJavaType resolveType(SchemaVariable sv, 
            SVSubstitute instCandidate, SVInstantiations instMap, Services services);
    
    
    
}
