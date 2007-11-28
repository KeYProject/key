// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.collection;



/** thrown if a duplicate is being added via addUnique() */
public class NotUniqueException extends Exception {
   Object offender;
   
   public NotUniqueException(Object o) {
      offender = o;
   }

   public String toString() {
      return "Tried to add a duplicate object to set. Offender is \n"+
      offender+"\nof class "+offender.getClass();
   }
}
