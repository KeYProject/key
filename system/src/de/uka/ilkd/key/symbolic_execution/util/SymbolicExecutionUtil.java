package de.uka.ilkd.key.symbolic_execution.util;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

/**
 * Provides utility methods for symbolic execution with KeY.
 * @author Martin Hentschel
 */
public final class SymbolicExecutionUtil {
   /**
    * Forbid instances.
    */
   private SymbolicExecutionUtil() {
   }
   
   /**
    * Creates a new default contract for the given {@link ProgramMethod}
    * which only ensures that the own invariants ({@code this.<inv>}) hold.
    * @param services The {@link Services} to use.
    * @param pm The {@link ProgramMethod} to create a default contract for.
    * @return The created {@link Contract}.
    * @throws SLTranslationException Occurred Exception.
    */
   public static FunctionalOperationContract createDefaultContract(Services services, ProgramMethod pm) throws SLTranslationException {
      // Create TextualJMLSpecCase
      ImmutableList<String> mods = ImmutableSLList.nil();
      mods = mods.append("public");
      TextualJMLSpecCase textualSpecCase = new TextualJMLSpecCase(mods, Behavior.NORMAL_BEHAVIOR);
      if (!pm.isStatic()) {
         textualSpecCase.addRequires(new PositionedString("this.<inv>")); // Assume own invariants
      }
      // Create contract
      JMLSpecFactory factory = new JMLSpecFactory(services);
      ImmutableSet<Contract> contracts = factory.createJMLOperationContracts(pm, textualSpecCase);
      return (FunctionalOperationContract)contracts.iterator().next();
   }
}
