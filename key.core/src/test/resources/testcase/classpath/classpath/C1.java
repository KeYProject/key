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

package cp;

public class C1 extends C {

  public static void m_C1() {
    that.is.going.to.be.discarded();
  }

  // cp.Unresolved2 must be a fully qualified reference!
  public cp.Unresolved2 q() {
    return null;
  }

}
