// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/* Enums are (partly) supported as well */

package cp;

enum E {
  e1(1), e2(20), e3(300);
  public static final E e4 = e2;
  E(int i) { }
}

