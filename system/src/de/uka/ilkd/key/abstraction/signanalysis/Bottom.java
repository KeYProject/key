package de.uka.ilkd.key.abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;

public class Bottom extends SignAnalysisDomainElem {

   private static final Bottom INSTANCE = new Bottom();
   
   private Bottom() {}
   
   public static Bottom getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("bottom");
   }

   @Override
   public Term getDefiningAxiom(ParsableVariable var, Services services) {
      TermBuilder tb = services.getTermBuilder();
      
      final Name freshVarName = new Name(tb.newName(var.sort()));
      services.getNamespaces().variables().add(new Named() {
         @Override
         public Name name() {
            return freshVarName;
         }
      });
      LogicVariable freshVar = new LogicVariable(freshVarName, var.sort());
      
      Term axiom = tb.equals(tb.var(var), tb.var(freshVar));
      axiom = tb.not(axiom);
      axiom = tb.all(freshVar, axiom);
      
      return axiom;
   }

}
