// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class Test {

   public static void main(String[] args) {
       FailedStaticInit fsi; 
       try { 
	   fsi = new FailedStaticInit();
       } catch (Error e) {
	   System.out.println("FailedStaticInit initialisation failed.");
       }
       fsi = A.SAVE;
       try {
	   fsi.objectMethod();
       } catch(Error e) {         	 
	   System.out.println("FailedStaticInit should be erroneous");
       }
       System.out.println("objectMethod worked: objectVar = "+fsi.objectVar);
   }
}
