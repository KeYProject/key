// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class SuperA {
  public int a = 3;
  public int b = a + 1;
  public int c;

  { a ++; }
  
  public SuperA() {
  } 

  public SuperA(int offset) {
     this();
     a+=offset;
  }
}
