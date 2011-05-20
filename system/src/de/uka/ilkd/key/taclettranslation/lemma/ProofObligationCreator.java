package de.uka.ilkd.key.taclettranslation.lemma;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.TacletFormula;
import de.uka.ilkd.key.taclettranslation.TacletVisitor;

public class ProofObligationCreator {
      

        

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
                UserDefinedSymbols symbolsForAxioms = analyzeTaclets(axioms,initConfig.namespaces());
                
                symbolsForAxioms.addSymbolsToNamespaces(initConfig.namespaces());
                
                for (Taclet taclet : taclets) {
                        listener.reportStatus(this, "Create Lemma for "
                                        + taclet.name());
                        singleProofs[i] = create(taclet, initConfig,symbolsForAxioms);
                        i++;
                }
                  ProofAggregate proofAggregate = singleProofs.length == 1 ? singleProofs[0]
                                : ProofAggregate.createProofAggregate(
                                                singleProofs,
                                                createName(singleProofs));
                // listener.progressStopped(this);
                listener.resetStatus(this);
                return proofAggregate;
        }
        
       

        
        private UserDefinedSymbols analyzeTaclets(ImmutableSet<Taclet> taclets, NamespaceSet referenceNamespaces){
              final UserDefinedSymbols userDefinedSymbols = new UserDefinedSymbols(referenceNamespaces,taclets);
                TacletVisitor visitor = new TacletVisitor() {
     
                @Override
                public void visit(Term visited) {
                     collectUserDefinedSymbols(visited, userDefinedSymbols);
                        
                }
              };
              for(Taclet taclet : taclets){
                      visitor.visit(taclet);
              }
              return userDefinedSymbols;
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
                                userDefinedSymbols.addVariable(term.op());
                        } 
                        if(term.op() instanceof SchemaVariable){
                                userDefinedSymbols.addSchemaVariable(term.op());
                        }
       
                }   
        }
        
  

        private ProofAggregate create(Taclet taclet,
                        InitConfig initConfig, UserDefinedSymbols symbolsForAxioms) {
                LemmaGenerator generator = new DefaultLemmaGenerator();
                TacletFormula formula = generator.translate(taclet,
                                initConfig.getServices());
                String name = "Taclet: " + taclet.name().toString();
                
                UserDefinedSymbols userDefinedSymbols = new UserDefinedSymbols(symbolsForAxioms);
                
                collectUserDefinedSymbols(formula.getFormula(), userDefinedSymbols);
   
                String header = userDefinedSymbols.createHeader(initConfig.getServices());
      
                Proof proof = new Proof(name, formula.getFormula(), header,
                                initConfig.createTacletIndex(),
                                initConfig.createBuiltInRuleIndex(),
                                initConfig.getServices());
         

                userDefinedSymbols.addSymbolsToNamespaces(proof.getNamespaces());
   
                return ProofAggregate.createProofAggregate(proof, name);
        }
        

        


}
