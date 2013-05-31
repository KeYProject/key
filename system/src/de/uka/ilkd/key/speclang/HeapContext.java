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


package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.java.Services;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;


/** Heap contexts are variaous scenarios of what happens to heap variables 
    during PO generation and built-in rule applications, like saving atPre heaps,
    anonymisation, etc.
  */
public class HeapContext {

  public static List<LocationVariable> getModHeaps(Services services, boolean transaction) {
      List<LocationVariable> result = new ArrayList<LocationVariable>();
      final LocationVariable savedHeap = services.getTypeConverter().getHeapLDT().getSavedHeap();
      for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
          if(savedHeap == heap && !transaction) {
              continue;
          }
          result.add(heap);
      }
      return result;
  }

  public static Map<LocationVariable,LocationVariable> getBeforeAtPreVars(List<LocationVariable> heaps, Services services, String contextName) {
    Map<LocationVariable,LocationVariable> result = new LinkedHashMap<LocationVariable,LocationVariable>();
    for(LocationVariable heap : heaps) {
       final LocationVariable atPreVar = TermBuilder.DF.heapAtPreVar(services, heap.name()+contextName, heap.sort(), true);
       result.put(heap, atPreVar);
    }
    return result;
  }

  public static Map<LocationVariable,Term> getAtPres(Map<LocationVariable,LocationVariable> atPreVars, Services services) {
    final Map<LocationVariable,Term> result = new LinkedHashMap<LocationVariable,Term>();
    for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
       final LocationVariable lv = atPreVars.get(heap);
       final Term t = lv == null ? null : TermBuilder.DF.var(lv);
       result.put(heap, t);
    }
    return result;
  }

}

