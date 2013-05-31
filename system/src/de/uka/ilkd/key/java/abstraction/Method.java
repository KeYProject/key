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


package de.uka.ilkd.key.java.abstraction;

/**
   A program model element representing methods.
 */
public interface Method extends Member, ClassTypeContainer {
    
    /**
       Checks if this member is abstract. A constructor will report
       <CODE>false</CODE>.
       @return <CODE>true</CODE> if this member is abstract,
       <CODE>false</CODE> otherwise.
       @see recoder.abstraction.Constructor
     */
    boolean isAbstract();

    /**
       Checks if this method is native. A constructor will report
       <CODE>false</CODE>.
       @return <CODE>true</CODE> if this method is native,
       <CODE>false</CODE> otherwise.
       @see recoder.abstraction.Constructor
     */
    boolean isNative();

    /**
       Checks if this method is synchronized. A constructor will report
       <CODE>false</CODE>.
       @return <CODE>true</CODE> if this method is synchronized,
       <CODE>false</CODE> otherwise.
       @see recoder.abstraction.Constructor
     */
    boolean isSynchronized();
    
}
