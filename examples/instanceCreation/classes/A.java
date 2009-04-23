// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class A extends SuperA {
  public int d;
  public int e = 3;

  public A() {
  }

  public A(int offset) {
     super(offset);
     a = a + e;
  }

}
