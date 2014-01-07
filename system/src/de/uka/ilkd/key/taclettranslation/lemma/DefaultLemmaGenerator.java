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

package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.taclettranslation.IllegalTacletException;
import de.uka.ilkd.key.taclettranslation.SkeletonGenerator;
import de.uka.ilkd.key.taclettranslation.TacletFormula;
import de.uka.ilkd.key.taclettranslation.TacletVisitor;

/**
 * The default lemma generator: Supports only certain types of
 * taclets. If a taclet is not supported, the generator throws 
 * an exception. 
 */
class DefaultLemmaGenerator implements LemmaGenerator {

        // Describes how a schema variable is mapped to another operator, e.g.
        // logical variable.
        private HashMap<SchemaVariable, Term> mapping = new LinkedHashMap<SchemaVariable, Term>();
       
        @Override
        public TacletFormula translate(Taclet taclet, Services services) {
                String result = checkTaclet(taclet);
                if(result != null){
                        throw new IllegalTacletException(result);
                }
                Term formula = SkeletonGenerator.DEFAULT_TACLET_TRANSLATOR
                                .translate(taclet);
                formula = rebuild(taclet, formula, services,
                                new LinkedHashSet<QuantifiableVariable>());
                result =   checkForIllegalOps(formula, taclet,false);
                if(result != null){
                        throw new IllegalTacletException(result);
                }
                return new LemmaFormula(taclet, formula);
        }
        
        private Term replace(Taclet taclet, Term term, Services services) {
                if (term.op() instanceof SchemaVariable) {
                        return getInstantiation(taclet,
                                        (SchemaVariable) term.op(), services);
                }

                return term;
        }
        
       public static String checkTaclet(final Taclet taclet){
           // This restriction no longer applies
           //    if(!(taclet instanceof FindTaclet)){
           //           return "Taclet is not of type FindTaclet";
           //    }
               String result = checkForIllegalConditions(taclet);
               if(result!=null) return result;
               TacletVisitor visitor = new TacletVisitor() {
                
                       @Override
                       public void visit(Term visited) {
                              String res = checkForIllegalOps(visited, taclet, true);
                              if(res !=null){
                                      failureOccurred(res);
                              }
                       }
               };
               
               return visitor.visit(taclet,true);
               
       }
        
       public static String checkForIllegalConditions(Taclet taclet){
                Iterator<VariableCondition> it = taclet.getVariableConditions();
                if(it.hasNext()){
                      return "The given taclet " + taclet.name() 
                                        + " contains variable conditions that are not supported.";    
                }
                return null;
        }
        
        public static String checkForIllegalOps(Term formula, Taclet owner, boolean schemaVarsAreAllowed){
             if((!schemaVarsAreAllowed && formula.op() instanceof SchemaVariable) ||
                formula.op() instanceof Modality ||
                formula.op() instanceof ModalOperatorSV ||
                formula.op() instanceof ProgramSV ||
                formula.op() instanceof SkolemTermSV ||
                formula.op() instanceof UpdateSV){
                     return "The given taclet " + owner.name() 
                                     + " contains a operator that is not allowed:\n"
                                     + formula.op().name();
             }
             for(Term sub : formula.subs()){
                     String s = checkForIllegalOps(sub, owner,schemaVarsAreAllowed);
                     if(s != null){
                             return s;
                     }
             }
             return null;
        }

        /**
         * Returns the instantiation for a certain schema variable, i.e. the
         * skolem term that is used for the instantiation.
         * 
         * @param owner
         *                The taclet the schema variable belongs to.
         * @param var
         *                The variable to be instantiated.
         * @param services
         * @return instantiation of the schema variable <code>var</code>.
         */
        protected final Term getInstantiation(Taclet owner, SchemaVariable var,
                        Services services) {
                Term instantiation = mapping.get(var);
                if (instantiation == null) {
                        instantiation = createInstantiation(owner, var,
                                        services);
                        mapping.put(var, instantiation);
                        
         
                }
                return instantiation;
        }

        /**
         * Returns the instantiation of <code>var</code>. In the case that an
         * instantiation does not exist it is created.
         * 
         * @param owner
         * @param var
         * @param services
         * 
         */
        private Term getInstantation(Taclet owner, VariableSV var,
                        Services services) {
                Term instantiation = mapping.get(var);
                if (instantiation == null) {
                        instantiation = createInstantiation(owner, var,
                                        services);
                        mapping.put(var, instantiation);
                }
                return instantiation;
        }

        private Term createInstantiation(Taclet owner, SchemaVariable sv,
                        Services services) {
                if (sv instanceof VariableSV) {
                        return createInstantiation(owner, (VariableSV) sv,
                                        services);
                }
                if (sv instanceof TermSV) {
                        return createInstantiation(owner, (TermSV) sv, services);
                }
                if (sv instanceof FormulaSV) {
                        return createInstantiation(owner, (FormulaSV) sv,
                                        services);
                }
                throw new IllegalTacletException(
                                "The taclet contains a schema variable which"
                                                + "is not supported.\n"
                                                + "Taclet: "
                                                + owner.name().toString()
                                                + "\n" + "SchemaVariable: "
                                                + sv.name().toString() + "\n");
        }

        /**
         * Creates the instantiation for a schema variable of type variable, i.e
         * a new logical variable is returned.
         * 
         * @param owner
         *                the taclet the schema variable belongs to.
         * @param sv
         *                the schema variable to be instantiated.
         * @param services
         *                some information about the proof currently considered.
         * @return a term that can be used for instantiating the schema
         *         variable.
         */
        private Term createInstantiation(Taclet owner, VariableSV sv,
                        Services services) {
                Name name = createUniqueName(services, "v_"+sv.name().toString());
                Sort sort = replaceSort(sv.sort(), services);
                LogicVariable variable = new LogicVariable(name, sort);
                return TermFactory.DEFAULT.createTerm(variable);
        }

        /**
         * Creates the instantiation for a schema variable of type term. Mainly
         * a skolem function is returned that depends on the prefix of
         * <code>sv</code>.
         */
        private Term createInstantiation(Taclet owner, TermSV sv,
                        Services services) {
                return createSimpleInstantiation(owner, sv, services);
        }

        /**
         * Creates the instantiation for a schema variable of type term. Mainly
         * a skolem function is returned that depends on the prefix of
         * <code>sv</code>.
         */
        private Term createInstantiation(Taclet owner, FormulaSV sv,
                        Services services) {
                return createSimpleInstantiation(owner, sv, services);
        }

        /**
         * Since only taclets are supported that contain only FOL-constituents,
         * there is no need to make it also dependend on program variables.
         * (See: Ensuring the Correctness of Lightweight Tactics for JavaCard
         * Dynamic Logic.) This method is used for both Formula schema variables
         * and Term schema variables.
         */
        private Term createSimpleInstantiation(Taclet owner, SchemaVariable sv,
                        Services services) {
                ImmutableSet<SchemaVariable> prefix = owner.getPrefix(sv)
                                .prefix();

                Sort[] argSorts = computeArgSorts(prefix, services);
                Term[] args = computeArgs(owner, prefix, services);
                Name name = createUniqueName(services, "f_"+sv.name().toString());

                Function function = new Function(name, replaceSort(sv.sort(), services), argSorts);
                return TermBuilder.DF.func(function, args);
        }

        private Name createUniqueName(Services services, String baseName) {
                return new Name(TermBuilder.DF.newName(services, baseName));
        }

        private Sort[] computeArgSorts(ImmutableSet<SchemaVariable> svSet, Services services) {
                Sort[] argSorts = new Sort[svSet.size()];
                int i = 0;
                for (SchemaVariable sv : svSet) {
                        argSorts[i] = replaceSort(sv.sort(), services);
                        i++;
                }
                return argSorts;
        }

        private Term[] computeArgs(Taclet owner,
                        ImmutableSet<SchemaVariable> svSet, Services services) {
                Term[] args = new Term[svSet.size()];
                int i = 0;
                for (SchemaVariable sv : svSet) {
                        args[i] = getInstantiation(owner, sv, services);
                        i++;
                }
                return args;
        }

        /**
         * Rebuilds a term recursively and replaces all schema variables with
         * skolem terms/variables. 
         *   */
        private Term rebuild(Taclet taclet, Term term, Services services,
                        HashSet<QuantifiableVariable> boundedVariables) {
                Term[] newSubs = new Term[term.arity()];
                int i = 0;
                LinkedList<QuantifiableVariable> qvars = new LinkedList<QuantifiableVariable>();
                for (QuantifiableVariable qvar : term.boundVars()) {
                        boundedVariables.add(qvar);
                        if (qvar instanceof VariableSV) {
                                qvars.add((QuantifiableVariable) getInstantation(
                                                taclet, (VariableSV) qvar,
                                                services).op());
                        }
                }

                for (Term sub : term.subs()) {
                        newSubs[i] = replace(taclet, sub, services);
                        // if(newSubs[i] == null){
                        // newSubs[i] = rebuild(taclet,sub,services);
                        newSubs[i] = rebuild(taclet, newSubs[i], services,
                                        boundedVariables);
                        // }
                        i++;
                }

                Operator newOp = replaceOp(term.op(), services);

                return TermFactory.DEFAULT
                                .createTerm(newOp,
                                                newSubs,
                                                new ImmutableArray<QuantifiableVariable>(
                                                                qvars), term
                                                                .javaBlock());
        }

        /**
         * Sometimes operators must be replaced during lemma generation.
         * Override this method to accomplish this in a subclass.
         *
         * <p>
         * By default, this method returns the argument <tt>op</tt>.
         *
         * @param op the operator to be replaced, not <code>null</code>
         * @param services A services object for lookups
         * @return the replacement operator, not <code>null</code>
         */
        protected Operator replaceOp(Operator op, Services services) {
            return op;
        }

        /**
         * Sometimes sorts must be replaced during lemma generation.
         * Override this method to accomplish this in a subclass.
         *
         * <p>
         * By default, this method returns the argument <tt>sort</tt>.
         *
         * @param sort the sort to be replaced, not <code>null</code>
         * @param services A services object for lookups
         * @return the replacement sort, not <code>null</code>
         */
        protected Sort replaceSort(Sort sort, Services services) {
            return sort;
        }
}