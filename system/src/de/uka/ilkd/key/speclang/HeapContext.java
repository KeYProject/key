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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.java.Services;

import java.util.List;
import java.util.Map;


/** Heap contexts are variaous scenarios of what happens to heap variables 
    during PO generation and built-in rule applications, like saving atPre heaps,
    anonymisation, etc.
  */
public interface HeapContext {

  public static final HeapContext METHOD_CONTRACT_HC = new MethodContractHeapContext(false);
  public static final HeapContext METHOD_CONTRACT_TR_HC = new MethodContractHeapContext(true);

  public static final HeapContext LOOP_HC = new MethodContractHeapContext(false);
  public static final HeapContext LOOP_TR_HC = new MethodContractHeapContext(true);

  Map<String,LocationVariable> getBeforeAtPreVars(Services services, String contextName);

  Map<String,Term> getAtPres();

  List<String> getModHeapNames();

  void reset();

}

