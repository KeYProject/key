// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.join;

import java.util.HashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.*;

/**
 * Rule that joins two sequents based on "total" weakening:
 * Replacement of symbolic state by an update setting every
 * program variable to a fresh Skolem constant, if the
 * respective program variable does not evaluate to the same
 * value in both states - in this case, the original value
 * is preserved (-> idempotency).
 * 
 * @author Dominic Scheurer
 */
public class JoinWeaken extends JoinProcedure {
   
    private static JoinWeaken INSTANCE = null;
    
    public static JoinWeaken instance() {
        if (INSTANCE == null) {
            INSTANCE = new JoinWeaken();
        }
        return INSTANCE;
    }
    
   private static final String DISPLAY_NAME = "JoinByFullAnonymization";
   
   @Override
   public Pair<HashSet<Term>, Term> joinValuesInStates(
         LocationVariable v,
         SymbolicExecutionState state1,
         Term valueInState1,
         SymbolicExecutionState state2,
         Term valueInState2,
         Services services) {
      
      final TermBuilder tb = services.getTermBuilder();
      
      final Function skolemConstant =
            getNewSkolemConstantForPrefix(v.name().toString(), v.sort(), services);

      return new Pair<HashSet<Term>, Term>(
            new HashSet<Term>(),
            tb.func(skolemConstant));
      
   }
   
   @Override
   public String toString() {
      return DISPLAY_NAME;
   }
}
