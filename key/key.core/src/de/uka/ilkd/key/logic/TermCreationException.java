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

package de.uka.ilkd.key.logic;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;

public class TermCreationException extends RuntimeException {

   public TermCreationException(String errorMessage) {
      super(errorMessage);
   }

   public TermCreationException(Operator op, Term failed) {
      super(getErrorMessage(op, failed));
   }

   private static String getErrorMessage(Operator op, Term failed) {
      ImmutableArray<Term> subs = failed.subs();
      for (int i = 0, n = subs.size(); i < n; i++) {
         Term sub = subs.get(i);
         assert sub == failed.subs().get(i);
      }

      return "Building a term failed. Normally there is an arity mismatch "
            + "or one of the subterms' sorts "
            + "is not compatible (e.g. like the \'2\' in \"true & 2\")\n"
            + "The top level operator was "
            + op
            + "(Sort: "
            + op.sort(subs)
            + ")"
            + (op instanceof SortedOperator ? "; its expected arg sorts were:\n"
                  + argsToString((SortedOperator) op)
                  : "") + "\nThe subterms were:\n" + subsToString(subs);
   }

   private static String argsToString(SortedOperator f) {
      StringBuffer sb = new StringBuffer();
      for (int i = 0; i < f.arity(); i++) {
         sb.append((i + 1) + ".) ");
         sb.append("sort: "
               + f.argSort(i)
               + (f.argSort(i) == null ? "" : ", sort hash: "
                     + f.argSort(i).hashCode()) + "\n");
      }
      return sb.toString();
   }

   private static String subsToString(ImmutableArray<Term> subs) {
      StringBuffer sb = new StringBuffer();
      for (int i = 0, n = subs.size(); i < n; i++) {
         sb.append((i + 1) + ".) ");
         Term subi = subs.get(i);
         if (subi != null) {
            sb.append(subi);
            Sort subiSort = subi.sort();
            if (subiSort != null) {
               sb.append("(sort: " + subi.sort() + ", sort hash: "
                     + subi.sort().hashCode() + ")\n");
            }
            else {
               sb.append("(Unknown sort, \"null pointer\")");
            }
         }
         else {
            sb.append(" !null!\n");
         }

      }
      return sb.toString();
   }
}
