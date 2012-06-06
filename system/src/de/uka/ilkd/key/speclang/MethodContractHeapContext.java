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
  private Map<LocationVariable,LocationVariable> lvCache = 
          new LinkedHashMap<LocationVariable,LocationVariable>();
  private List<LocationVariable> heapMods;

  MethodContractHeapContext(boolean transaction) {
    this.transaction = transaction;
  }

  public Map<LocationVariable,LocationVariable> getBeforeAtPreVars(Services services, String contextName) {
    lvCache.clear();
    final LocationVariable savedHeap = services.getTypeConverter().getHeapLDT().getSavedHeap();
    for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
       if(savedHeap == heap && !transaction) {
         continue;
       }
       final LocationVariable atPreVar = TermBuilder.DF.heapAtPreVar(services, heap.name()+contextName, true);
       lvCache.put(heap, atPreVar);
    }
    return lvCache;
  }

  public Map<LocationVariable,Term> getAtPres(Services services) {
    assert !lvCache.isEmpty();
    final Map<LocationVariable,Term> result = new LinkedHashMap<LocationVariable,Term>();
    for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
       final LocationVariable lv = lvCache.get(heap);
       final Term t = lv == null ? null : TermBuilder.DF.var(lv);
       result.put(heap, t);
    }
    return result;
  }

  public List<LocationVariable> getModHeaps(Services services) {
      heapMods = new ArrayList<LocationVariable>();      
      final LocationVariable savedHeap = services.getTypeConverter().getHeapLDT().getSavedHeap();
      for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
          if(savedHeap == heap && !transaction) {
              continue;
          }
          heapMods.add(heap);
      }
      return heapMods;
  }

  public void reset() {
      lvCache.clear();
  }


}

