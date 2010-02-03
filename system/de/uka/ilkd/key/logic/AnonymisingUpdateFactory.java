// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.PairOfTermAndListOfName;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.util.Debug;


/**
 * Creates anonymising updates for sets of locations, i.e. (quantified) updates
 * which assign uninterpreted functions to all locations of such a set.
 */
public class AnonymisingUpdateFactory {
    private static final TermBuilder TB = TermBuilder.DF;
    private static final TermFactory TF = TermFactory.DEFAULT;
    private final UpdateFactory uf;
    
    private final Term updateTarget =
        TB.func ( new NonRigidFunction ( new Name ( "x" ), Sort.FORMULA,
                                         new Sort [0] ) );
    
    public AnonymisingUpdateFactory(UpdateFactory uf) {
        this.uf = uf;
    }

    
    private static Term[] getSubTerms(Term term) {
        int arity = term.arity();
        Term[] result = new Term[arity];
        
        for(int i = 0; i < arity; i++) {
            result[i] = term.sub(i);
        }
        
        return result;
    }
    
    
    private static Name getNewName(Services services, Name baseName, Name proposal) {
        NamespaceSet namespaces = services.getNamespaces();
        
        int i = 0;
        Name name;
        if (proposal != null && namespaces.lookup(proposal) == null) {
            name = proposal;
        } else {
            do {
                name = new Name(baseName + "_" + i++);
            } while(namespaces.lookup(name) != null);
        }

        return name;
    }
       
    
    /**
     * Determines the arguments sorts of the passed operator
     * (helper for getUninterpretedFunction()).
     */
    private static Sort[] getArgumentSorts(Operator op,
                                           Sort[] commonArguments,
                                           Services services) {
        if (op.arity() == 0) return commonArguments;
        
        final Sort[] result = new Sort[op.arity() + commonArguments.length];
        System.arraycopy ( commonArguments, 0, result, op.arity (),
                           commonArguments.length );
        
        if(op instanceof ProgramVariable) {
            Debug.assertTrue(op.arity() == 0);
        } else if(op instanceof AccessOp) {
            Sort integerSort = services.getTypeConverter().getIntegerLDT()
                                                          .targetSort();

            if(op instanceof AttributeOp) {
                AttributeOp aop = (AttributeOp) op;
                KeYJavaType kjt = ((ProgramVariable) aop.attribute())
                                  .getContainerType();
                if(services.getJavaInfo().rec2key().getSuperArrayType() == kjt
                   && "length".equals(aop.attribute().name().toString())) {
                    result[0] 
                         = services.getJavaInfo().getJavaLangObjectAsSort();
                } else {
                    result[0] = kjt.getSort();
                }
            } else if(op instanceof ArrayOp) {
                result[0] = ((ArrayOp)op).arraySort();
                result[1] = integerSort;
            } else {
                Debug.fail("Unexpected location operator."+op);
            }

            if(((AccessOp)op).isShadowed()) {
                result[op.arity() - 1] = integerSort; 
            }
        } else if(op instanceof Function) {           
            Function func = (Function) op;               
            for(int i = 0; i < op.arity(); i++) {
                result[i] = func.argSort(i);
            }
        } else {
            Debug.fail("Unsupported location operator."+op);  
        }
        
        return result;
    }
    
    private static Term[] getArguments(Term locTerm, Term[] commonArguments) {
        final Operator op = locTerm.op ();
        if ( op.arity () == 0 ) return commonArguments;

        final Term[] argTerms = new Term [op.arity () + commonArguments.length];
        System.arraycopy ( getSubTerms ( locTerm ), 0, argTerms, 0, op.arity () );
        System.arraycopy ( commonArguments, 0, argTerms, op.arity (),
                           commonArguments.length );
        return argTerms;
    }

    
    /**
     * Gets an uninterpreted function for the passed location term 
     * (helper for createUninterpretedFunctions()).
     */
    private static RigidFunction getUninterpretedFunction(
                                Term locTerm, 
                                Sort[] commonArguments,
                                Map<Operator, RigidFunction> functions,
                                Services services, Name proposal) {
        RigidFunction result = (RigidFunction) functions.get(locTerm.op());
        
        if (result == null) {
            Name baseName = locTerm.op() instanceof AttributeOp ? 
                    ((AttributeOp) locTerm.op()).attribute().name()
                    : locTerm.op() instanceof ArrayOp ? new Name("get")
                            : locTerm.op().name();

            if (baseName instanceof ProgramElementName) {
                baseName = new 
                    Name(((ProgramElementName)baseName).getProgramName());
            }
            
            String s = baseName.toString();
            if (s.startsWith("<") && s.endsWith(">")) {
                baseName = new Name(s.substring(1, s.length() - 1));
            }

            result = new RigidFunction ( getNewName ( services, baseName,
                                         proposal ), locTerm.sort (),
                                         getArgumentSorts ( locTerm.op (),
                                                            commonArguments,
                                                            services ) );
            services.getNamespaces().functions().add(result);
            functions.put(locTerm.op(), result);
        }
        
        return result;
    }
    
    
    /**
     * Creates suitable uninterpreted functions for the passed locations.
     */
    public static RigidFunction[] createUninterpretedFunctions(
                                            LocationDescriptor[] locations,
                                            Sort[] commonArguments,
                                            Services services,
                                            Name[] proposals) {
        RigidFunction[] result = new RigidFunction[locations.length];
        Map<Operator, RigidFunction> functions = new HashMap<Operator, RigidFunction>();
        
        for(int i = 0, c = 0; i < locations.length; i++) {
            if(locations[i] instanceof BasicLocationDescriptor) {
                BasicLocationDescriptor bloc 
                        = (BasicLocationDescriptor) locations[i];
                Name proposal = null;
                if (proposals != null && proposals.length > c) proposal = proposals[c++];
                result[i] = getUninterpretedFunction(bloc.getLocTerm(),
                                                     commonArguments,
                                                     functions,
                                                     services,
                                                     proposal);
            } else {
                Debug.assertTrue(
                        locations[i] instanceof EverythingLocationDescriptor
                        && commonArguments.length == 0,
                        "Modifies set {" + locations[i] + "} is not allowed in this situation " +
                        "(could be because of metavariables that have to be given as arguments," +
                        "which is not supported for the modifier *)");
                result[i] = null;
            }
        }
        
        return result;
    }

    /**
     * Creates suitable uninterpreted functions for the passed locations.
     */
    public static RigidFunction[] createUninterpretedFunctions(
                                            LocationDescriptor[] locations,
                                            Sort[] commonArguments,
                                            Services services) {
        return createUninterpretedFunctions(locations, commonArguments, services, null);
    }

    /**
     * Creates suitable uninterpreted functions for the passed locations.
     */
    public static RigidFunction[] createUninterpretedFunctions(
                                             LocationDescriptor[] locations,
                                             Services services) {
        return createUninterpretedFunctions(locations, new Sort [0], services);
    }
    
    /**
     * Creates the anonymising update for the passed locations using the passed
     * uninterpreted functions (which must have the correct signature).
     */
    public Update createAnonymisingUpdate(LocationDescriptor[] locations,
                                          Function[] functions,
                                          Services services) {
        return createAnonymisingUpdate ( locations, functions, new Term [0],
                                         services );
    }
    
      
    private Update createAnonymisingUpdate(LocationDescriptor[] locations,
                                           Function[] functions,
                                           Term[] commonArguments,
                                           Services services) {
        Debug.assertTrue ( functions.length == locations.length );

        Update result = uf.skip ();

        for(int i = 0; i < locations.length; i++) {
            if(locations[i] instanceof BasicLocationDescriptor) {
                BasicLocationDescriptor bloc 
                        = (BasicLocationDescriptor) locations[i];
                final Term locTerm = bloc.getLocTerm();
                final Term guardTerm = bloc.getFormula();
                
                //create elementary update
                final Term[] argTerms =
                    getArguments ( locTerm, commonArguments );
                
                Term valueTerm = TF.createFunctionTerm(functions[i], argTerms);
                Update elementaryUpdate = uf.elementaryUpdate(locTerm, 
                                                              valueTerm);
                
                //create guarded update
                Update guardedUpdate = uf.guard(guardTerm, elementaryUpdate);
                
                //create quantified update
                Update quantifiedUpdate = guardedUpdate;
                IteratorOfQuantifiableVariable it = locTerm.freeVars().iterator();
                while(it.hasNext()) {
                    quantifiedUpdate = uf.quantify(it.next(), quantifiedUpdate);
                }
                //add update to result update
                result = uf.parallel(result, quantifiedUpdate);                
            } else {
                Debug.assertTrue(
                        locations[i] instanceof EverythingLocationDescriptor);
                
                //create anonym*ous* update
                AnonymousUpdate ao = AnonymousUpdate.getNewAnonymousOperator();
                Term updateTerm = TF.createAnonymousUpdateTerm(ao, TF.createJunctorTerm(Op.TRUE));
                return Update.createUpdate(updateTerm);
            }
        }

        return result;        
    }

    /**
     * Creates the anonymising update for the passed locations using new
     * uninterpreted functions.
     */
    public Update createAnonymisingUpdate(SetOfLocationDescriptor locations,
                                          Services services) {
        return createAnonymisingUpdate(locations, new Term[0], services);
    }
    
    
    public Update createAnonymisingUpdate(SetOfLocationDescriptor locations,
                                          Term[] commonArguments,
                                          Services services) {
        LocationDescriptor[] locationsArray = locations.toArray();
        RigidFunction[] functions 
            = createUninterpretedFunctions(locationsArray,
                                           extractSorts(commonArguments),
                                           services);
        return createAnonymisingUpdate(locationsArray, 
                                       functions, 
                                       commonArguments, 
                                       services);
    }
    
    
    /**
     * Creates the anonymising update for the passed locations using the passed
     * uninterpreted functions (which must have the correct signature) and 
     * applies it to the passed target term.
     */
    public Term createAnonymisingUpdateTerm(LocationDescriptor[] locations,
                                            Function[] functions,
                                            Term targetTerm,
					    Services services) {
        return uf.prepend(createAnonymisingUpdate(locations, functions, services),
                        targetTerm);
    }
    
    
    /**
     * Creates the anonymising update for the passed locations using new
     * uninterpreted functions and applies it to the passed target term.
     */
    public Term createAnonymisingUpdateTerm(SetOfLocationDescriptor locations,
                                            Term targetTerm,
                                            Services services) {
        LocationDescriptor[] locationsArray = locations.toArray();
        RigidFunction[] functions = createUninterpretedFunctions(locationsArray,
                                                                 services);
        return createAnonymisingUpdateTerm ( locationsArray, functions,
                                             targetTerm, services );
    }
    
    /**
     * Creates the anonymising update for the passed locations using new
     * uninterpreted functions and applies it to the passed target term.
     */
    public Term createAnonymisingUpdateAsFor(LocationDescriptor[] locationsArray,
                                             Term[] commonArguments,
                                             Services services) {
        return createAnonymisingUpdateAsFor(locationsArray, commonArguments,
                services, null).getTerm();
    }

    /**
     * Creates the anonymising update for the passed locations using new
     * uninterpreted functions and applies it to the passed target term.
     */
    public PairOfTermAndListOfName createAnonymisingUpdateAsFor(
                                             LocationDescriptor[] locationsArray,
                                             Term[] commonArguments,
                                             Services services,
                                             Name[] proposals) {
        RigidFunction[] functions =
            createUninterpretedFunctions ( locationsArray,
                                           extractSorts ( commonArguments ),
                                           services,
                                           proposals );
        Update upd = createAnonymisingUpdate ( locationsArray, functions,
                                               commonArguments, services );
        ListOfName genNames = SLListOfName.EMPTY_LIST;

        for (int i = 0; i < functions.length; i++) {
            if (functions[i] != null)
                genNames = genNames.append(functions[i].name());
        }

        return new PairOfTermAndListOfName(uf.prepend ( upd, updateTarget ),
                genNames);
    }
    
    private Sort[] extractSorts(Term[] argTerms) {
        final Sort[] argSorts = new Sort [argTerms.length];
        for ( int i = 0; i != argTerms.length; ++i )
            argSorts[i] = argTerms[i].sort ();
        return argSorts;
    }
}
