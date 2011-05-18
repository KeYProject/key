package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.Collection;
import java.util.Comparator;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeSet;

import com.sun.org.apache.xml.internal.resolver.helpers.Namespaces;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.TacletFormula;

public class ProofObligationCreator {
      
        private static class UserDefinedSymbols{
                private final Set<Named> usedExtraFunctions = new TreeSet<Named>(NamedComparator.INSTANCE);
                private final Set<Named> usedExtraPredicates = new TreeSet<Named>(NamedComparator.INSTANCE);
                private final  Set<Named> usedExtraSorts     = new TreeSet<Named>(NamedComparator.INSTANCE);
                private final Set<Named> usedExtraVariables  = new TreeSet<Named>(NamedComparator.INSTANCE);
                private final NamespaceSet referenceNamespaces;
                                               
                public UserDefinedSymbols(NamespaceSet referenceNamespaces) {
                        super();
                        this.referenceNamespaces = referenceNamespaces;
                }

                private void addUserDefiniedSymbol(Named symbol, Set<Named> set, Namespace excludeNamespace){
                        if(!set.contains(symbol) && excludeNamespace.lookup(symbol.name()) == null){
                            set.add(symbol);       
                        }
                }
                
                public void addFunction(Named symbol){
                        addUserDefiniedSymbol(symbol, usedExtraFunctions,referenceNamespaces.functions());
                }
                public void addPredicate(Named symbol){
                        addUserDefiniedSymbol(symbol, usedExtraPredicates,referenceNamespaces.functions());
                }
                public void addSort(Named symbol){
                        addUserDefiniedSymbol(symbol, usedExtraSorts,referenceNamespaces.sorts());
                }
                public void addVariables(Named symbol){
                        addUserDefiniedSymbol(symbol, usedExtraVariables,referenceNamespaces.variables());
                }
        }
        
        private static class NamedComparator implements Comparator<Named>{
                static NamedComparator INSTANCE = new NamedComparator();
                @Override
                public int compare(Named o1, Named o2) {
                        return o1.name().compareTo(o2.name());
                }
                
        }
        

        private String createName(ProofAggregate[] singleProofs) {
                return "Side proofs for " + singleProofs.length + " lemmata.";
        }
        
        

        public ProofAggregate create(ImmutableSet<Taclet> taclets,
                        InitConfig initConfig, ImmutableSet<Taclet> axioms,
                        ProblemInitializerListener listener) {
                initConfig.setTaclets(initConfig.getTaclets().union(axioms));
                ProofAggregate[] singleProofs = new ProofAggregate[taclets
                                .size()];
                int i = 0;
                listener.progressStarted(this);
                for (Taclet taclet : taclets) {
                        listener.reportStatus(this, "Create Lemma for "
                                        + taclet.name());
                        singleProofs[i] = create(taclet, initConfig);
                        i++;
                }
                System.out.println(createCommonHeader(taclets));
                ProofAggregate proofAggregate = singleProofs.length == 1 ? singleProofs[0]
                                : ProofAggregate.createProofAggregate(
                                                singleProofs,
                                                createName(singleProofs));
                // listener.progressStopped(this);
                listener.resetStatus(this);
                return proofAggregate;
        }
        
       
        private String createCommonHeader(ImmutableSet<Taclet> taclets){
                StringBuffer buffer = new StringBuffer();
                for(Taclet taclet : taclets){
                      buffer.append("\n\n");
                      buffer.append(createHeaderFor(taclet));
                }
                String result = buffer.toString();
                result = result.replaceAll("\\[", "");
                result = result.replaceAll("\\]", "");
                return result;
        }
        
        private StringBuffer createHeaderFor(Taclet taclet){
                StringBuffer buffer = new StringBuffer();
                
                return new StringBuffer(taclet.toString());
        }

        
        private void completeNamespaces(Proof proof, UserDefinedSymbols userDefinedSymbols) {
                final NamespaceSet namespaces = proof.getNamespaces();
                
                addToNamespace(userDefinedSymbols.usedExtraFunctions,namespaces.functions());
                addToNamespace(userDefinedSymbols.usedExtraPredicates,namespaces.functions());
                addToNamespace(userDefinedSymbols.usedExtraVariables,namespaces.variables());
                addToNamespace(userDefinedSymbols.usedExtraSorts,namespaces.sorts());
               
                
                System.out.println();
                for(Named named : userDefinedSymbols.usedExtraFunctions){
                        System.out.print(named.name()+", " );
                }
                System.out.println();
                for(Named named : userDefinedSymbols.usedExtraPredicates){
                        System.out.print(named.name()+", " );
                }
                System.out.println();
                for(Named named : userDefinedSymbols.usedExtraSorts){
                        System.out.print(named.name()+", " );
                }
        }
        
        private String createHeader(UserDefinedSymbols userDefinedSymbols){
                StringBuffer result = new StringBuffer();
                result.append(createHeaderFor("\\sorts", userDefinedSymbols.usedExtraSorts));
                result.append("\n\n");
                result.append(createHeaderFor("\\functions", userDefinedSymbols.usedExtraFunctions));
                result.append("\n\n");
                result.append(createHeaderFor("\\predicates", userDefinedSymbols.usedExtraPredicates));
                return result.toString();
        }
        
        private StringBuffer createHeaderFor(String type,Set<Named> symbols){
                StringBuffer buffer = new StringBuffer(type);
                buffer.append("{");
                for(Named symbol : symbols){
                        buffer.append("\n");
                        if(symbol instanceof SortedOperator){
                            Sort sort = ((SortedOperator)symbol).sort();
                            if(sort != Sort.FORMULA){
                                    buffer.append(sort.name()+" ");
                            }
                        }
                        buffer.append(symbol.name());
                        if(symbol instanceof Function){
                                Function op = (Function) symbol;
                                for(int i=0; i <  op.arity(); i++){
                                       buffer.append(i==0?"(":",");
                                       buffer.append(op.argSort(i));
                                       buffer.append(i==op.arity()-1?")":"");
                                }
                        }
                        buffer.append(";");
                }
                buffer.append("\n}");
                return buffer;
        }
        
        
        private void collectUserDefinedSymbols(Term term, UserDefinedSymbols userDefinedSymbols){
                for(Term sub : term.subs()){
                        collectUserDefinedSymbols(sub, userDefinedSymbols);
                }  
                if(term.op() instanceof SortedOperator){
                        Sort sort = ((SortedOperator)term.op()).sort();
                        userDefinedSymbols.addSort(sort);
                        
                        if(term.op() instanceof Function){
                                if(sort == Sort.FORMULA){
                                     userDefinedSymbols.addPredicate(term.op());
                                }else{
                                     userDefinedSymbols.addFunction(term.op());  
                                }                                      
                        }
                        if(term.op() instanceof LogicVariable){
                                userDefinedSymbols.addVariables(term.op());
                        } 
       
                }   
        }
        
  

        private ProofAggregate create(Taclet taclet,
                        InitConfig initConfig) {
                LemmaGenerator generator = new DefaultLemmaGenerator();
                TacletFormula formula = generator.translate(taclet,
                                initConfig.getServices());
                String name = "Taclet: " + taclet.name().toString();
                
                UserDefinedSymbols userDefinedSymbols = new UserDefinedSymbols(initConfig.namespaces());
                
                collectUserDefinedSymbols(formula.getFormula(), userDefinedSymbols);
                System.out.println(createHeader(userDefinedSymbols));
                Proof proof = new Proof(name, formula.getFormula(), "",
                                initConfig.createTacletIndex(),
                                initConfig.createBuiltInRuleIndex(),
                                initConfig.getServices());
                System.out.println("NEW PROOF");

                
                completeNamespaces(proof,userDefinedSymbols);
                
                return ProofAggregate.createProofAggregate(proof, name);
        }
        
        private void addToNamespace(Collection<Named> symbols, Namespace namespace){
                for(Named symbol : symbols){
                        Named named = namespace.lookup(symbol.name());

                        if(named != symbol && named != null){
                                throw new RuntimeException("Name is already in namespace: "+ symbol.name());
                        }
                        if(named == null){
                                System.out.println("add: "+symbol.name());
                                namespace.add(symbol);
                        }
                        if(named == symbol){
                                System.out.println("Exists already: "+ named.name());
                        }
                }
        }
        


}
