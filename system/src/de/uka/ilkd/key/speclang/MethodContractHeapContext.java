// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.java.Services;

import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.LinkedHashMap;

public class MethodContractHeapContext implements HeapContext {
 
  private boolean transaction;
  private Map<String,LocationVariable> lvCache = new LinkedHashMap<String,LocationVariable>();
  private List<String> heapModNames = new ArrayList<String>();

  MethodContractHeapContext() {
    this(false);
  }

  MethodContractHeapContext(boolean transaction) {
    this.transaction = transaction;
    for(String heapName : TermBuilder.VALID_HEAP_NAMES) {
       if(TermBuilder.SAVED_HEAP_NAME.equals(heapName) && !transaction) {
         continue;
       }
       heapModNames.add(heapName);
    }
  }

  public Map<String,LocationVariable> getBeforeAtPreVars(Services services, String contextName) {
    lvCache.clear();
    for(String heapName : TermBuilder.VALID_HEAP_NAMES) {
       if(TermBuilder.SAVED_HEAP_NAME.equals(heapName) && !transaction) {
         continue;
       }
       final LocationVariable atPreVar = TermBuilder.DF.heapAtPreVar(services, heapName+"Before_" + contextName, true);
       lvCache.put(heapName, atPreVar);
    }
    return lvCache;
  }

  public Map<String,Term> getAtPres() {
    assert !lvCache.isEmpty();
    final Map<String,Term> result = new LinkedHashMap<String,Term>();
    for(String heapName : TermBuilder.VALID_HEAP_NAMES) {
       final LocationVariable lv = lvCache.get(heapName);
       final Term t = lv == null ? null : TermBuilder.DF.var(lv);
       result.put(heapName, t);
    }
    return result;
  }

  public List<String> getModHeapNames() {
    return heapModNames;
  }

  public void reset() {
   lvCache.clear();
  }


}

